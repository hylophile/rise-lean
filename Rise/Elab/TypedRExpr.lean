import Rise.Basic
import Rise.Elab.RElabM
import Rise.Elab.Type
import Rise.Unification.MM
import Rise.Unification.MVars
import Rise.Elab.TypedRExprBase
import Lean
open Lean Elab Meta

/-- For each leading implicit parameter, remove it and replace each occurrence with the same fresh mvar. -/
partial def implicitsToMVars (t: RType) : RElabM RType := do
  match t with
  | .pi bk .implicit un b => do
    let mid ← getFreshMVarId
    addMVar mid un bk none
    let newB := b.supplyMVar mid
    implicitsToMVars newB
  | x => return x

/-- Lean.Meta.evalExpr is unsafe, but we use it in elabToTypedRExpr. -/
@[implemented_by evalExpr]
opaque unsafeEvalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

/-- Main elaboration function for Rise expressions. -/
partial def elabToTypedRExpr : Syntax → RElabM TypedRExpr
  | `(rise_expr| $l:num$[$s:rise_expr_numlit_suffix]?) => do
    match s with
    | .some suffix => match suffix with
      | `(rise_expr_numlit_suffix| int) => return ⟨.lit (.int l.getNat), .data <| .scalar .int⟩
      | `(rise_expr_numlit_suffix| i8)  => return ⟨.lit (.int l.getNat), .data <| .scalar .i8⟩
      | `(rise_expr_numlit_suffix| i16) => return ⟨.lit (.int l.getNat), .data <| .scalar .i16⟩
      | `(rise_expr_numlit_suffix| i32) => return ⟨.lit (.int l.getNat), .data <| .scalar .i32⟩
      | `(rise_expr_numlit_suffix| i64) => return ⟨.lit (.int l.getNat), .data <| .scalar .i64⟩
      | `(rise_expr_numlit_suffix| u8)  => return ⟨.lit (.int l.getNat), .data <| .scalar .u8⟩
      | `(rise_expr_numlit_suffix| u16) => return ⟨.lit (.int l.getNat), .data <| .scalar .u16⟩
      | `(rise_expr_numlit_suffix| u32) => return ⟨.lit (.int l.getNat), .data <| .scalar .u32⟩
      | _                               => throwErrorAt suffix s!"unknown integer suffix {suffix}"
    | .none => return ⟨.lit (.int l.getNat), .data <| .scalar .int⟩
    
  | `(rise_expr| $l:scientific$[$s:rise_expr_scilit_suffix]?) => do
    match s with
    | .some suffix => match suffix with
      | `(rise_expr_scilit_suffix| float) => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩
      | `(rise_expr_scilit_suffix| f16)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f16⟩
      | `(rise_expr_scilit_suffix| f32)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f32⟩
      | `(rise_expr_scilit_suffix| f64)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f64⟩
      | _                                 => throwErrorAt suffix s!"unknown float suffix {suffix}"
    | .none => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩

  | `(rise_expr| $i:ident) => do
    let ltctx ← getLocalTCtx
    let gtctx ← getGlobalTCtx
    -- todo: use findLocal? and findConst? here
    match ltctx.reverse.zipIdx.find? (λ ((name, _t), _id) => name == i.getId) with
      | some ((name, t), index) =>
        return ⟨.bvar index name, t⟩
      | none => match gtctx.reverse.zipIdx.find? (λ ((name, _t), _id) => name == i.getId) with
        | some ((_name, t), _index) =>
          return ⟨.const i.getId, t⟩
        | none => throwErrorAt i s!"unknown identifier {i.getId}"

  | `(rise_expr| fun ($x:ident) => $b:rise_expr) => do
    let id ← getFreshMVarId
    addMVar id Lean.Name.anonymous RKind.data
    let t :=  RType.data (.mvar id Lean.Name.anonymous)
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b
    return ⟨.lam x.getId t b, .fn t b.type⟩

  | `(rise_expr| fun ( $x:ident : $t:rise_type ) => $b:rise_expr) => do
    let t ← elabToRType t
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b
    return ⟨.lam x.getId t b, .fn t b.type⟩

  | `(rise_expr| fun ( $x:ident : $k:rise_kind ) => $b:rise_expr) => do
    let k ← elabToRKind k
    let b ← withNewTypeVar (x.getId, k) do elabToTypedRExpr b
    return ⟨.deplam x.getId k b, .pi k .explicit x.getId b.type⟩

  | `(rise_expr| fun { $x:ident : $k:rise_kind } => $b:rise_expr) => do
    let k ← elabToRKind k
    let b ← withNewTypeVar (x.getId, k) do elabToTypedRExpr b
    return ⟨.deplam x.getId k b, .pi k .implicit x.getId b.type⟩

  | `(rise_expr| $f_syn:rise_expr $e_syn:rise_expr) => do
      let f ← elabToTypedRExpr f_syn
      let f := {f with type := (← implicitsToMVars f.type)}
      let e ← elabToTypedRExpr e_syn
      let e := {e with type := (← implicitsToMVars e.type)}
      match f.type with
      | .fn blt brt => do
        addUnifyGoal (blt, e.type)
        match ← blt.unify e.type with
        | .ok sub =>
          addSubst f_syn sub
          return ⟨.app f e, brt⟩
        | .error x =>
          logErrorAt f_syn s!"\ncannot unify application of '{f_syn.raw.prettyPrint}' to '{e_syn.raw.prettyPrint}':\n{blt} != {e.type}\n{x}"
          return ⟨.app f e, brt⟩
      | _ => throwErrorAt f_syn s!"expected a function type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

  | `(rise_expr| $f_syn:rise_expr $n:rise_nat) => do
    let n ← elabToRNat n
    let f ← elabToTypedRExpr f_syn
    let f := {f with type := (← implicitsToMVars f.type)}
    match f.type with
    | .pi .nat .explicit _ b =>
      let bt := b.supplyRNat n
      return ⟨.depapp f <| .nat n, bt⟩
    | _ => throwErrorAt f_syn s!"expected a nat pi type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

  | `(rise_expr| $f_syn:rise_expr $d:rise_data) => do
    let d ← elabToRData d
    let f ← elabToTypedRExpr f_syn
    let f := {f with type := (← implicitsToMVars f.type)}
    match f.type with
    | .pi .data .explicit _ b =>
      let bt := b.supplyRData d
      return ⟨.depapp f <| .data d, bt⟩
    | _ => throwErrorAt f_syn s!"expected a data pi type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

  | `(rise_expr| $f_syn:rise_expr ($x:ident ↦ $n:rise_nat)) => do
    let f ← elabToTypedRExpr f_syn
    let f := {f with type := (← implicitsToMVars f.type)}
    let n ← withNewTypeVar (x.getId, RKind.nat2nat) do elabToRNat n
    match f.type with
    | .pi .nat2nat .explicit _ b =>
      -- let b := b.supplyNat2Nat d
      return ⟨.depapp f <| .nat2nat ⟨x.getId, n⟩, b⟩
    | _ => throwErrorAt f_syn s!"expected a nat2nat pi type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

  -- | `(rise_expr| $f_syn:rise_expr ($x:ident ↦ $d:rise_data)) => do
  --   let f ← elabToTypedRExpr f_syn
  --   let f := {f with type := (← implicitsToMVars f.type)}
  --   let d ← withNewTypeVar (x.getId, RKind.nat2nat) do elabToRData d
  --   match f.type with
  --   | .pi .nat2data .explicit _ b =>
  --     -- let b := b.supplyNat2Data d
  --     return ⟨.depapp f <| .nat2data ⟨x.getId, d⟩, b⟩
  --   | _ => throwErrorAt f_syn s!"expected a nat2data pi type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

  | stx =>
    match stx with
    | .node _ `choice choices => do
      -- dbg_trace choices.map (·.getArgs) |>.map (fun x => x.map (·.getKind.toString))
      let cs := choices.map (·.getArgs)
      -- match choices[0]! with
      -- | `(rise_expr| $e:rise_expr) =>
      if cs.all (·.size == 2) then -- app ambiguity
        let e1_syn := cs[0]![0]!
        let expr ← elabToTypedRExpr e1_syn -- could improve this double elab by refactoring (adding functions which elab nat-app/data-app which left expr already elabbed)
        let expr := {expr with type := (← implicitsToMVars expr.type)}
        -- let seconds := cs.map (·[1]! |>.getKind)
        let nat_syn := cs.findIdx? (·[1]!.getKind.toString.startsWith "rise_nat")
        let data_syn := cs.findIdx? (·[1]!.getKind.toString.startsWith "rise_data")
        let expr_syn := cs.findIdx? (·[1]!.getKind.toString.startsWith "rise_expr")
        -- dbg_trace nat_syn
        -- dbg_trace ("aaa", seconds)
        -- dbg_trace cs
        -- dbg_trace expr.type
        -- dbg_trace (nat_syn, data_syn, expr_syn, expr_syn)
        match expr.type with
        | .fn .. => elabToTypedRExpr choices[expr_syn.get!]!
        | .pi .nat .. => elabToTypedRExpr choices[nat_syn.get!]!
        | .pi .data .. => elabToTypedRExpr choices[data_syn.get!]!
        | _ => throwError "invalid expr type, unreachable"
      else throwError "unhandled ambiguous syntax"
    -- Use Lean's context to reuse definitions (e.g. $matmul) of other Rise programs.
    | .node _ `rise_expr.pseudo.antiquot xs
    | .node _ `rise_decl.pseudo.antiquot xs =>
      match xs[2]? with
      | some x => match x with
        | `($x:ident) => do
          let env ← getEnv
          let name ← resolveGlobalConstNoOverload x
          let some decl := env.find? name
            | throwError "definition {name} not found"
          match decl.value? with
          | some v =>
            let v ← unsafeEvalExpr TypedRExpr (mkConst ``TypedRExpr) v
            -- todo: Shifting mvars is not necessary once we start prohibiting Rise programs that contain mvars.
            shiftMVars v
          | none => throwError "?!?"
        | _=> throwError "???"
      | none => throwError "!!!"
    | stx =>
      throwErrorAt stx s!"unexpected rise expr syntax:\n{stx}"

def elabTypedRExpr (stx : Syntax) : RElabM Expr := do
  let rexpr ← elabToTypedRExpr stx
  return toExpr rexpr

elab "[RiseTE|" e:rise_expr "]" : term => do
  let p ← liftMacroM <| expandMacros e
  liftToTermElabM <| elabTypedRExpr p

-- #eval [RiseTE| (fun x => x) 3]
--
-- #pp [RiseTE| (fun t u : data => (fun v : data => fun x : v×u => x) t)]
