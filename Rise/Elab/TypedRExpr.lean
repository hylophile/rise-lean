import Rise.Basic
import Rise.Elab.RElabM
import Rise.Elab.Type
import Rise.Unification.MM
import Rise.Unification.MVars
import Lean
open Lean Elab Meta

instance : ToExpr RLit where
  toExpr
    | .bool b => mkAppN (mkConst ``RLit.bool) #[toExpr b]
    | .int i => mkAppN (mkConst ``RLit.int) #[toExpr i]
    | .float f => mkAppN (mkConst ``RLit.float) #[toExpr f]
  toTypeExpr := mkConst ``RLit

instance : ToExpr RNat2Nat where
  toExpr v := mkAppN (mkConst ``RNat2Nat.mk) #[toExpr v.binderName, toExpr v.body]
  toTypeExpr := mkConst ``RNat2Nat

instance : ToExpr RNat2Data where
  toExpr v := mkAppN (mkConst ``RNat2Data.mk) #[toExpr v.binderName, toExpr v.body]
  toTypeExpr := mkConst ``RNat2Data

instance : ToExpr RWrapper where
  toExpr
    | .nat b => mkAppN (mkConst ``RWrapper.nat) #[toExpr b]
    | .data i => mkAppN (mkConst ``RWrapper.data) #[toExpr i]
    | .nat2nat v => toExpr v
    | .nat2data v => toExpr v
    | .addrSpace a => mkAppN (mkConst ``RWrapper.addrSpace) #[toExpr a]
  toTypeExpr := mkConst ``RWrapper

mutual
partial
def TypedRExpr.toExpr (e : TypedRExpr) : Expr  :=
    let nodeExpr := e.node.toExpr
    let typeExpr := ToExpr.toExpr e.type
    mkAppN (mkConst ``TypedRExpr.mk) #[nodeExpr, typeExpr]

partial
def TypedRExprNode.toExpr : TypedRExprNode → Expr
    | .lit n =>
        mkAppN (mkConst ``TypedRExprNode.lit) #[toExpr n]
    | .bvar index name =>
        mkAppN (mkConst ``TypedRExprNode.bvar) #[mkNatLit index, toExpr name]
    | .const name =>
        mkAppN (mkConst ``TypedRExprNode.const) #[toExpr name]
    | .lam name t body =>
        mkAppN (mkConst ``TypedRExprNode.lam) #[toExpr name, toExpr t, body.toExpr]
    | .deplam name kind body =>
        mkAppN (mkConst ``TypedRExprNode.deplam) #[toExpr name, toExpr kind, body.toExpr]
    | .app e1 e2 =>
        mkAppN (mkConst ``TypedRExprNode.app) #[e1.toExpr, e2.toExpr]
    | .depapp e1 e2 =>
        mkAppN (mkConst ``TypedRExprNode.depapp) #[e1.toExpr, toExpr e2]
end

instance : ToExpr TypedRExpr where
  toExpr := TypedRExpr.toExpr
  toTypeExpr := mkConst ``TypedRExpr

instance : ToExpr TypedRExprNode where
  toExpr := TypedRExprNode.toExpr
  toTypeExpr := mkConst ``TypedRExprNode

declare_syntax_cat rise_expr_numlit_suffix
syntax "int" : rise_expr_numlit_suffix
syntax "i8"  : rise_expr_numlit_suffix
syntax "i16" : rise_expr_numlit_suffix
syntax "i32" : rise_expr_numlit_suffix
syntax "i64" : rise_expr_numlit_suffix
syntax "u8"  : rise_expr_numlit_suffix
syntax "u16" : rise_expr_numlit_suffix
syntax "u32" : rise_expr_numlit_suffix
syntax "u64" : rise_expr_numlit_suffix


declare_syntax_cat rise_expr_scilit_suffix
syntax "float" : rise_expr_scilit_suffix
syntax "f16"   : rise_expr_scilit_suffix
syntax "f32"   : rise_expr_scilit_suffix
syntax "f64"   : rise_expr_scilit_suffix

declare_syntax_cat                                            rise_expr
syntax num         (noWs rise_expr_numlit_suffix)?          : rise_expr
syntax scientific  (noWs rise_expr_scilit_suffix)?          : rise_expr
syntax ident                                                : rise_expr
syntax "fun" "(" ident+ (":" rise_type)? ")" "=>" rise_expr : rise_expr
syntax "fun"     ident+ (":" rise_type)?     "=>" rise_expr : rise_expr
syntax "fun" "(" ident+ (":" rise_kind)  ")" "=>" rise_expr : rise_expr
syntax "fun" "{" ident+ (":" rise_kind)  "}" "=>" rise_expr : rise_expr
syntax "fun"     ident+ ":" rise_kind        "=>" rise_expr : rise_expr
syntax "let" ident ":=" rise_expr "in" rise_expr : rise_expr
syntax:10 rise_expr:10 "+" rise_expr:11                     : rise_expr
syntax:20 rise_expr:20 "*" rise_expr:21                     : rise_expr
syntax rise_expr ".1" : rise_expr
syntax rise_expr ".2" : rise_expr


-- nat2nat
syntax:50 rise_expr:50 "(" ident "↦" rise_nat ")"           : rise_expr
syntax:50 rise_expr:50 "(" ident "↦" rise_data ")"          : rise_expr

syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:50 rise_expr:50 rise_nat                             : rise_expr
syntax:50 rise_expr:50 rise_data                            : rise_expr
syntax:40 rise_expr:40 "|>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 "<|" rise_expr:41                    : rise_expr
syntax:41 rise_expr:41 ">>" rise_expr:42                    : rise_expr
syntax:41 rise_expr:41 "<<" rise_expr:42                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

macro_rules
  | `(rise_expr| let $x:ident := $v:rise_expr in $b:rise_expr) =>
    `(rise_expr| ((fun $x:ident => $b) $v:rise_expr))
  | `(rise_expr| fun $x:ident => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident) => $b:rise_expr)

  | `(rise_expr| fun $x:ident : $t:rise_type => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident : $t:rise_type) => $b:rise_expr )

  | `(rise_expr| fun $x:ident : $t:rise_kind => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident : $t:rise_kind) => $b:rise_expr )

  | `(rise_expr| fun $x:ident $y:ident $xs:ident* => $e:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun $x => fun $y => $e)
    | _ =>
      `(rise_expr| fun $x => fun $y => fun $xs* => $e)

  | `(rise_expr| fun $x:ident $y:ident $xs:ident* : $k:rise_type => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => fun ($xs* : $k:rise_type) => $b:rise_expr)
  | `(rise_expr| fun ($x:ident $y:ident $xs:ident* : $k:rise_type) => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => fun ($xs* : $k:rise_type) => $b:rise_expr)
  | `(rise_expr| fun ($x:ident $y:ident $xs:ident* : $k:rise_kind) => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => fun ($xs* : $k:rise_kind) => $b:rise_expr)
  | `(rise_expr| fun {$x:ident $y:ident $xs:ident* : $k:rise_kind} => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => $b:rise_expr)
    | _ =>
      `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => fun {$xs* : $k:rise_kind} => $b:rise_expr)
  | `(rise_expr| fun  $x:ident $y:ident $xs:ident* : $k:rise_kind  => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => fun ($xs* : $k:rise_kind) => $b:rise_expr)


  | `(rise_expr| $f:rise_expr >> $g:rise_expr) =>
    let x := mkIdent `x
    `(rise_expr| fun $x => $g ($f $x:ident))

  | `(rise_expr| $f:rise_expr << $g:rise_expr) =>
    `(rise_expr| $g >> $f)
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    `(rise_expr| $f:rise_expr $e:rise_expr)
  | `(rise_expr| $f:rise_expr <| $e:rise_expr) => do
    `(rise_expr| $f:rise_expr $e:rise_expr)
  | `(rise_expr| ($e:rise_expr)) => do
    `(rise_expr| $e)

set_option hygiene false in
macro_rules
  | `(rise_expr| $a:rise_expr + $b:rise_expr) =>
    `(rise_expr| (add $a:rise_expr $b:rise_expr))
  | `(rise_expr| $a:rise_expr * $b:rise_expr) =>
    `(rise_expr| (mul $a:rise_expr $b:rise_expr))
  | `(rise_expr| $x:rise_expr.1) =>
    `(rise_expr| (fst $x:rise_expr))
  | `(rise_expr| $x:rise_expr.2) =>
    `(rise_expr| (snd $x:rise_expr))

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

  | `(rise_expr| $f_syn:rise_expr ($x:ident ↦ $d:rise_data)) => do
    let f ← elabToTypedRExpr f_syn
    let f := {f with type := (← implicitsToMVars f.type)}
    let d ← withNewTypeVar (x.getId, RKind.nat2nat) do elabToRData d
    match f.type with
    | .pi .nat2data .explicit _ b =>
      -- let b := b.supplyNat2Data d
      return ⟨.depapp f <| .nat2data ⟨x.getId, d⟩, b⟩
    | _ => throwErrorAt f_syn s!"expected a nat2data pi type for '{f_syn.raw.prettyPrint}', but found: {toString f.type}"

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
