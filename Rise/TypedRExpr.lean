import Rise.Basic
import Rise.RElabM
import Rise.Type
import Lean
open Lean Elab

declare_syntax_cat rise_expr_numlit_suffix
-- syntax "nat" : rise_expr_numlit_suffix
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
syntax num (rise_expr_numlit_suffix)?                       : rise_expr
syntax "(" rise_nat ":" "nat" ")" : rise_expr
syntax "(" rise_data ":" "data" ")" : rise_expr
syntax scientific (rise_expr_scilit_suffix)?                : rise_expr
syntax ident                                                : rise_expr
syntax "?" ident                                                : rise_expr
syntax "fun" "(" ident+ (":" rise_type)? ")" "=>" rise_expr : rise_expr
syntax "fun"     ident+ (":" rise_type)?     "=>" rise_expr : rise_expr
syntax "fun" "(" ident+ (":" rise_kind)  ")" "=>" rise_expr : rise_expr
syntax "fun"     ident+ (":" rise_kind)      "=>" rise_expr : rise_expr
syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:40 rise_expr:40 "|>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 ">>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 "<<" rise_expr:41                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

-- set_option pp.raw true
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
    `(rise_expr| $f $e)
  | `(rise_expr| ($e:rise_expr)) => do
    `(rise_expr| $e)


partial def addImplicits (t: RType) : RElabM RType := do
  match t with
  | .pi bk .implicit un b => do
    let mid ← getFreshMVarId
    addMVar mid un bk none
    let newB := b.bvar2mvar mid
    addImplicits newB
  | x => return x

partial def elabToTypedRExpr : Syntax → RElabM TypedRExpr
  | `(rise_expr| $l:num $[$s:rise_expr_numlit_suffix]?) => do
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
      | _                               => throwErrorAt suffix s!"unknown suffix {suffix}"
    | .none => return ⟨.lit (.int l.getNat), .data <| .scalar .int⟩
      -- let _ ← Term.addTermInfo l (toExpr t.toString) -- meh
  | `(rise_expr| $l:scientific $[$s:rise_expr_scilit_suffix]?) => do
    match s with
    | .some suffix => match suffix with
      | `(rise_expr_scilit_suffix| float) => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩
      | `(rise_expr_scilit_suffix| f16)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f16⟩
      | `(rise_expr_scilit_suffix| f32)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f32⟩
      | `(rise_expr_scilit_suffix| f64)   => return ⟨.lit (.float (toString l)), .data <| .scalar .f64⟩
      | _                                 => throwErrorAt suffix s!"unknown suffix {suffix}"
    | .none => return ⟨.lit (.float (toString l)), .data <| .scalar .float⟩
  | `(rise_expr| ($n:rise_nat : nat)) => do
    let n ← elabToRNat n
    return ⟨.nat n, .data .natType⟩

  -- | `(rise_expr| ($d:rise_data : data)) => do
    

  | `(rise_expr| ? $_i:ident) => do
    return ⟨.mvar `testing, .data <| .mvar 0 `testing⟩
  | `(rise_expr| $i:ident) => do
    let ltctx ← getLTCtx
    let gtctx ← getGTCtx
    -- todo: use findLocal? and findConst? here
    match ltctx.reverse.zipIdx.find? (λ ((name, _t), _id) => name == i.getId) with
      | some ((_name, t), index) =>
        return ⟨.bvar index, t⟩
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

  -- we could have also used only one app instead of app and depapp, but then we need to extend rexpr such that a single rnat, rdata, rtype... is also an rexpr, because app takes two rexpr. but then a single rdata is a valid rexpr (e.g. `f32`), which doesn't make sense. so instead, we will parse something like `($f ($t:rtype : $k:rkind))
  -- (TODO: insert depapp implementation here)
  | `(rise_expr| $f_syn:rise_expr $e_syn:rise_expr ) => do
      let f ← elabToTypedRExpr f_syn
      let f := {f with type := (← addImplicits f.type)}
      let e ← elabToTypedRExpr e_syn
      let e := {e with type := (← addImplicits e.type)}
      match f.type with
      | .fn blt brt =>
        match blt.unify e.type with
        | some sub =>
          addSubst sub
          return ⟨.app f e, brt.apply sub⟩
        | none =>
          logErrorAt f_syn s!"\ncannot unify application of '{f_syn.raw.prettyPrint}' to '{e_syn.raw.prettyPrint}':\n{blt} != {e.type}"
          -- logErrorAt e_syn s!"\ncannot unify {blt} with {e.type}"
          throwError "unification failed"
      | .pi _ .implicit _ _ =>
        throwError s!"unexpected implicit pi {f.type}"
      | .pi .data .explicit _ _ =>
        throwErrorAt f_syn s!"i haven't seen this case yet: {f.type}"
      | .pi .nat .explicit _ b =>
        match e.node, e.type with
        | .nat n, .data .natType =>
          let bt :=  b.rnatbvar2rnat n
          return ⟨.app f e, bt⟩
        | _, _ =>
          throwErrorAt e_syn "TODO, found {e.type}"
      | _ => throwErrorAt f_syn s!"expected a function type for ({f_syn.raw.prettyPrint}), but found: {repr f.type}"
      -- return TypedRExpr.app e1 e2

  | e => throwErrorAt e s!"unexpected rise expr syntax:\n{e}" --throwUnsupportedSyntax

instance : ToExpr RLit where
  toExpr
    | .bool b => mkAppN (mkConst ``RLit.bool) #[toExpr b]
    | .int i => mkAppN (mkConst ``RLit.int) #[toExpr i]
    | .float f => mkAppN (mkConst ``RLit.float) #[toExpr f]
  toTypeExpr := mkConst ``RLit


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
    | .nat n =>
        mkAppN (mkConst ``TypedRExprNode.nat) #[toExpr n]
    | .bvar index =>
        mkAppN (mkConst ``TypedRExprNode.bvar) #[mkNatLit index]
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
end

instance : ToExpr TypedRExpr where
  toExpr := TypedRExpr.toExpr
  toTypeExpr := mkConst ``TypedRExpr

instance : ToExpr TypedRExprNode where
  toExpr := TypedRExprNode.toExpr
  toTypeExpr := mkConst ``TypedRExprNode

def elabTypedRExpr (stx : Syntax) : RElabM Expr := do
  let rexpr ← elabToTypedRExpr stx
  return toExpr rexpr

elab "[RiseTE|" e:rise_expr "]" : term => do
  let p ← liftMacroM <| expandMacros e
  liftToTermElabM <| elabTypedRExpr p

#eval IO.println <| toString [RiseTE| fun a : int → int => a 10000].node
#check [RiseTE| fun a : int → int → int => a 10000 2]
#check [RiseTE| 3]
#check [RiseTE| 3]
#check [RiseTE| 3u32]
#check [RiseTE| 3.0f32]


-- --set_option pp.explicit true
-- #check [RiseE| fun as => as]
-- #check [RiseE| fun as bs => as]
-- #check [RiseE| fun as bs cs => as]
-- #check [RiseE| fun as => fun bs => (as bs)]
-- #check [RiseE| fun as => fun bs => as bs (fun c => c)]
-- #check [RiseE| fun as => as (fun as => as)]

-- #check [RiseE| fun x => x]

-- #check [RiseE| fun(x : nat) => 3]

-- -- trying to use x at term level. it's not legal,
-- -- because x is only in the kinding context
-- -- #check [RiseE| fun(x : nat) => x]

-- #check [RiseE| fun(x : 5·scalar) => x]

-- #check [RiseE| fun(x : nat) => 3]

-- -- TODO: do we want to parse this as n being an implicit parameter?
-- #check [RiseE| fun(n : nat) => fun(x : n·scalar) => x]


-- def TypedRExpr.bvar2fvar (e : TypedRExpr) (un : Lean.Name) : TypedRExpr :=
--   go un e 0 where
--   go (un : Lean.Name) (e : TypedRExpr) (n : Nat) : TypedRExpr :=
--   match e with
--   | .bvar i => if i == n then .fvar un else e
--   | .fvar .. => e
--   | .const .. => e
--   | .lit .. => e
--   | .app fn arg => .app (go un fn n) (go un arg n)
--   | .lam lun bt b => .lam lun bt (go un b (n+1))
--   | .deplam lun bt b => .deplam lun bt (go un b (n+1))



-- -- -- TODO: translate example programs in shine/src/test/scala/rise/core
-- -- -- /home/n/tub/masters/shine/src/test/scala/apps
-- -- --
-- -- --
-- --
-- --
