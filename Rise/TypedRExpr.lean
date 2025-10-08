import Rise.Basic
import Rise.RElabM
import Rise.Type
import Lean
open Lean Elab Meta


-- #eval runEgg "hi"



instance : ToExpr RLit where
  toExpr
    | .bool b => mkAppN (mkConst ``RLit.bool) #[toExpr b]
    | .int i => mkAppN (mkConst ``RLit.int) #[toExpr i]
    | .float f => mkAppN (mkConst ``RLit.float) #[toExpr f]
  toTypeExpr := mkConst ``RLit

instance : ToExpr RWrapper where
  toExpr
    | .nat b => mkAppN (mkConst ``RWrapper.nat) #[toExpr b]
    | .data i => mkAppN (mkConst ``RWrapper.data) #[toExpr i]
    | .type f => mkAppN (mkConst ``RWrapper.type) #[toExpr f]
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
    | .fvar name =>
        mkAppN (mkConst ``TypedRExprNode.fvar) #[toExpr name]
    | .mvar name =>
        mkAppN (mkConst ``TypedRExprNode.mvar) #[toExpr name]
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


-- 
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
syntax "?" ident                                            : rise_expr
syntax "fun" "(" ident+ (":" rise_type)? ")" "=>" rise_expr : rise_expr
syntax "fun"     ident+ (":" rise_type)?     "=>" rise_expr : rise_expr
syntax "fun" "(" ident+ (":" rise_kind)  ")" "=>" rise_expr : rise_expr
syntax "fun" "{" ident+ (":" rise_kind)  "}" "=>" rise_expr : rise_expr
syntax "fun"     ident+ ":" rise_kind        "=>" rise_expr : rise_expr
syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:50 rise_expr:50 rise_nat:51             : rise_expr
syntax:50 rise_expr:50 rise_data:51           : rise_expr
syntax:40 rise_expr:40 "|>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 ">>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 "<<" rise_expr:41                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

set_option pp.raw true
-- set_option pp.raw.maxDepth 10

macro_rules
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

  -- | `(rise_expr| fun {$x:ident $y:ident $xs:ident* : $k:rise_kind} => $b:rise_expr) =>
  --   match xs with
  --   | #[] =>
  --     `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => $b:rise_expr)
  --   | _ =>
  --     `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => fun {$xs* : $k:rise_kind} => $b:rise_expr)

  | `(rise_expr| $f:rise_expr >> $g:rise_expr) =>
    let x := mkIdent `x
    `(rise_expr| fun $x => $g ($f $x:ident))

  | `(rise_expr| $f:rise_expr << $g:rise_expr) =>
    `(rise_expr| $g >> $f)
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    `(rise_expr| $f:rise_expr $e:rise_expr)
  | `(rise_expr| ($e:rise_expr)) => do
    `(rise_expr| $e)

def syn2str (stx : Syntax) : Std.Format :=
  match stx with
  | .node _ `choice choices =>
    choices[0]!.prettyPrint
  | stx => stx.prettyPrint

-- takes an expr with possibly conflicting mvarIds and maps them to fresh mvarIds in the current context.
def shiftMVars (e : TypedRExpr) : RElabM TypedRExpr := do
  let mvars := e.type.collectMVarIds
  let map : Std.HashMap RMVarId RMVarId ← mvars.foldM (init := Std.HashMap.emptyWithCapacity)
    (fun m a => do
      let x ← getFreshMVarId
      pure <| m.insert a x)
  return e.mapTypeMVars (fun id => map[id]!)

partial def addImplicits (t: RType) : RElabM RType := do
  match t with
  | .pi bk .implicit un b => do
    let mid ← getFreshMVarId
    addMVar mid un bk none
    let newB := b.bvar2mvar mid
    addImplicits newB
  | x => return x

unsafe def elabToTypedRExpr : Syntax → RElabM TypedRExpr
  | `(rise_expr| $l:num$[$s:rise_expr_numlit_suffix]?) => do
    match s with
    | .some suffix => match suffix with
      -- | `(rise_expr_numlit_suffix| nat) => return ⟨.lit (.nat l.getNat), .data .natType⟩
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
      -- let _ ← Term.addTermInfo l (toExpr t.toString) -- meh
  | `(rise_expr| $l:scientific$[$s:rise_expr_scilit_suffix]?) => do
    match s with
    | .some suffix => match suffix with
      | `(rise_expr_scilit_suffix| float) => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩
      | `(rise_expr_scilit_suffix| f16)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f16⟩
      | `(rise_expr_scilit_suffix| f32)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f32⟩
      | `(rise_expr_scilit_suffix| f64)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f64⟩
      | _                                 => throwErrorAt suffix s!"unknown float suffix {suffix}"
    | .none => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩

  | `(rise_expr| ? $_i:ident) => do
    return ⟨.mvar `testing, .data <| .mvar 0 `testing⟩
  | `(rise_expr| $i:ident) => do
    let ltctx ← getLTCtx
    let gtctx ← getGTCtx
    -- todo: use findLocal? and findConst? here
    match ltctx.reverse.zipIdx.find? (λ ((name, _t), _id) => name == i.getId) with
      | some ((name, t), index) =>
        return ⟨.bvar index name, t⟩
      | none => match gtctx.reverse.zipIdx.find? (λ ((name, _t), _id) => name == i.getId) with
        | some ((_name, t), _index) =>
          return ⟨.const i.getId, t⟩
        | none => throwErrorAt i s!"unknown identifier {i.getId}"

  | `(rise_expr| fun ($x:ident) => $b:rise_expr ) => do
    let id ← getFreshMVarId
    addMVar id Lean.Name.anonymous RKind.data
    let t :=  RType.data (.mvar id Lean.Name.anonymous)
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b
    let t ← applyUnifyResultsUntilStable t
    return ⟨.lam x.getId t b, .fn t b.type⟩

  | `(rise_expr| fun ( $x:ident : $t:rise_type ) => $b:rise_expr ) => do
    let t ← elabToRType t
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b
    return ⟨.lam x.getId t b, .fn t b.type⟩

  | `(rise_expr| fun ( $x:ident : $k:rise_kind ) => $b:rise_expr ) => do
    let k ← elabToRKind k
    let b ← withNewTVar (x.getId, k) do elabToTypedRExpr b
    return ⟨.deplam x.getId k b, .pi k .explicit x.getId b.type⟩

  | `(rise_expr| fun { $x:ident : $k:rise_kind } => $b:rise_expr ) => do
    let k ← elabToRKind k
    let b ← withNewTVar (x.getId, k) do elabToTypedRExpr b
    return ⟨.deplam x.getId k b, .pi k .implicit x.getId b.type⟩

  | `(rise_expr| $f_syn:rise_expr $e_syn:rise_expr ) => do
      let f ← elabToTypedRExpr f_syn
      let f := {f with type := (← addImplicits f.type)}
      let e ← elabToTypedRExpr e_syn
      let e := {e with type := (← addImplicits e.type)}
      match f.type with
      | .fn blt brt =>
        match blt.unify e.type with
        | .ok sub =>
          -- let x := runEgg s!"(~ {blt.toSExpr} {e.type.toSExpr})"
          -- let x := runEgg RNat.toSMTLib 
          -- dbg_trace x
          addSubst sub
          return ⟨.app f e, brt.apply sub⟩
        | .error x =>
          logErrorAt f_syn s!"\ncannot unify application of '{syn2str f_syn}' to '{syn2str e_syn}':\n{blt} != {e.type}\n{x}"
          -- logErrorAt e_syn s!"\ncannot unify application of '{syn2str f_syn}' to '{syn2str e_syn}':\n{blt} != {e.type}"
          throwError "unification failed"
      | _ => throwErrorAt f_syn s!"expected a function type for '{syn2str f_syn}', but found: {toString f.type}"

  | `(rise_expr| $f_syn:rise_expr $n:rise_nat) => do
    let n <- elabToRNat n
    let f <- elabToTypedRExpr f_syn
    let f := {f with type := (← addImplicits f.type)}
    match f.type with
    | .pi .nat .explicit _ b =>
      let bt := b.rnatbvar2rnat n
      return ⟨.depapp f <| .nat n, bt⟩
    | _ => throwErrorAt f_syn s!"expected a pi type for '{syn2str f_syn}', but found: {toString f.type}"

  | `(rise_expr| $f_syn:rise_expr $d:rise_data) => do
    let d ← elabToRData d
    let f <- elabToTypedRExpr f_syn
    let f := {f with type := (← addImplicits f.type)}
    match f.type with
    | .pi .data .explicit _ b =>
      let bt := b.rdatabvar2rdata d
      return ⟨.depapp f <| .data d, bt⟩
    | _ => throwErrorAt f_syn s!"expected a pi type for '{syn2str f_syn}', but found: {toString f.type}"
    
  | stx =>
    match stx with
    | .node _ `choice choices => do
      -- dbg_trace choices
      let results ← choices.mapM (fun c =>
        try
          Except.ok <$> elabToTypedRExpr c
        catch e => do
          return Except.error e)
      match results.partition (·.isOk) with
      | (#[.ok res], _) => return res
      | (#[], errs) => do
        errs.forM (fun err => match err with
        | .error e => logErrorAt stx e.toMessageData
        | _ => throwError "unreachable"
        ) 
        throwErrorAt stx "Only found errors under all interpretations"
      | _ => throwError "Multiple interpretations possible. Haven't seen this case yet though"
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
            let v ← evalExpr TypedRExpr (mkConst ``TypedRExpr) v
            shiftMVars v
          | none => throwError "?!?"
        | _=> throwError "???"
      | none => throwError "!!!"
    | stx =>
      throwErrorAt stx s!"unexpected rise expr syntax:\n{stx}"

unsafe def elabTypedRExpr (stx : Syntax) : RElabM Expr := do
  let rexpr ← elabToTypedRExpr stx
  return toExpr rexpr

elab "[RiseTE|" e:rise_expr "]" : term => unsafe do
  let p ← liftMacroM <| expandMacros e
  liftToTermElabM <| elabTypedRExpr p

-- #eval IO.println <| toString [RiseTE| fun a : int → int => a 10000].node
-- #check [RiseTE| fun a : int → int → int => a 10000 2]
-- #check [RiseTE| 3]
--
def abc := [RiseTE| fun x => x]

#eval toString [RiseTE| fun x => $abc].type

-- #check [RiseTE| 3u32]
-- #check [RiseTE| 3.0f32]
-- #eval toJson [RiseTE| fun x: f32 → f32 → f32 => x 5.0f32 3.0f32]
-- #eval toJson [RiseTE| fun x: f32 → f32 → f32 => (x 5.0f32) 3.0f32]
-- #eval toJson [RiseTE| fun x: f32 → f32 → f32 => x 5.0f32 (3.0f32)]
-- #eval toJson [RiseTE| (fun n: nat => fun x : f32 => x) (3+5) 5.0f32]
-- #eval toJson [RiseTE| (fun n: nat => fun x : f32 => x) 3 5.0f32]


-- dependent application demo

-- #eval toJson [RiseTE| (fun n: nat => fun x : n·f32 => x) 3]

-- #eval toJson [RiseTE| (fun d: data => fun x : d => x) f32]


-- #check [RiseTE| fun as => as]
-- #check [RiseTE| fun as bs => as]
-- #eval toJson [RiseTE| fun as bs cs => as]
-- #check [RiseTE| fun as: f32 → f32 => fun bs => (as bs)]
-- #check [RiseTE| fun as => (fun as => as)]

-- #check [RiseTE| fun x => x]

-- #check [RiseTE| fun(x : nat) => 3]
-- #check [RiseTE| fun(x : data) => 3]

-- -- -- trying to use x at term level. it's not legal,
-- -- -- because x is only in the kinding context
-- -- #check [RiseTE| fun(x : nat) => x]



-- -- -- TODO: translate example programs in shine/src/test/scala/rise/core
-- -- -- /home/n/tub/masters/shine/src/test/scala/apps
-- -- --
-- -- --
-- --
-- --
