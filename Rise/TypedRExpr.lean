import Rise.Prelude
import Rise.RElabM
import Rise.Type
import Lean
open Lean Elab


declare_syntax_cat rise_expr
syntax num                                                  : rise_expr
syntax ident                                                : rise_expr
syntax "fun" "(" ident (":" rise_type)? ")" "=>" rise_expr  : rise_expr
syntax "fun"     ident+ (":" rise_type)?     "=>" rise_expr  : rise_expr
syntax "fun" "(" ident (":" rise_kind)  ")" "=>" rise_expr  : rise_expr
syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:40 rise_expr:40 "|>" rise_expr:41                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

set_option pp.raw true
set_option pp.raw.maxDepth 10
macro_rules
  | `(rise_expr| fun $x:ident $y:ident $xs:ident* => $e:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun $x => fun $y => $e)
    | _ =>
      `(rise_expr| fun $x => fun $y => fun $xs* => $e)


partial def addImplicits (t: RType) : RElabM RType := do
  match t with
  | .upi bk .im un b => do
    let mid ← getFreshMVarId
    addMVar mid un bk none
    let newB := b.bvar2mvar mid
    addImplicits newB
  | x => return x

partial def elabToTypedRExpr : Syntax → RElabM TypedRExpr
  | `(rise_expr| $l:num) => do
    let t : RType := .data .scalar
    -- let _ ← Term.addTermInfo l (toExpr t.toString) -- meh
    return ⟨.lit l.getNat, t⟩

  | `(rise_expr| $i:ident) => do
    let ltctx ← getLTCtx
    let gtctx ← getGTCtx
    -- todo: use findLocal? and findConst? here
    match ltctx.reverse.zipIdx.find? (λ ((name, t), id) => name == i.getId) with
      | some ((name, t), index) =>
        return ⟨.bvar index, t⟩
      | none => match gtctx.reverse.zipIdx.find? (λ ((name, t), id) => name == i.getId) with
        | some ((name, t), index) =>
          return ⟨.const i.getId, t⟩
        | none => throwErrorAt i s!"unknown identifier {i.getId}"

  | `(rise_expr| fun $x:ident => $b:rise_expr )
  | `(rise_expr| fun ($x:ident) => $b:rise_expr ) => do
    let id ← getFreshMVarId
    addMVar id Lean.Name.anonymous RKind.data
    let t :=  RType.data (.mvar id Lean.Name.anonymous)
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b

    -- let body := body.bvar2fvar un -- why does this call cause "fail to show termination?"
    let t ← applyUnifyResultsUntilStable t
    -- let bodyt ← applyUnifyResults bodyt
    return ⟨.lam x.getId t b, .pi t b.type⟩

    -- let b ← withNewLocalTerm (x.getId, none) do elabToTypedRExpr b
    --
    -- return TypedRExpr.lam x.getId none b

  | `(rise_expr| fun $x:ident : $t:rise_type => $b:rise_expr )
  | `(rise_expr| fun ( $x:ident : $t:rise_type ) => $b:rise_expr ) => do
    let t ← elabToRType t
    let b ← withNewLocalTerm (x.getId, t) do elabToTypedRExpr b
    return ⟨.lam x.getId t b, .pi t b.type⟩

  -- | `(rise_expr| fun ( $x:ident : $k:rise_kind ) => $b:rise_expr ) => do
  --   let k ← elabToRKind k
  --   let b ← withNewTVar (x.getId, some k) do elabToTypedRExpr b
  --   return TypedRExpr.ulam x.getId (some k) b

  | `(rise_expr| $fs:rise_expr $e:rise_expr ) => do
      let f ← elabToTypedRExpr fs
      let f := {f with type := (← addImplicits f.type)}
      let e ← elabToTypedRExpr e
      let e := {e with type := (← addImplicits e.type)}
      match f.type with
      | .pi blt brt =>
        match blt.unify e.type with
        | some sub =>
          addSubst sub
          return ⟨.app f e, brt.apply sub⟩
          -- applyUnifyResults brt
        | none =>
          throwError s!"\ncannot unify {blt} with {e.type}"
      | .upi bk .im un b =>
        throwError s!"unexpected upi {f.type}"
      | _ => throwErrorAt fs s!"expected a function type for ({Lean.Syntax.prettyPrint fs}), but found: {f.type}"
      -- return TypedRExpr.app e1 e2

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f $e)
    elabToTypedRExpr s

  | `(rise_expr| ( $e:rise_expr )) => do
    let s ← `(rise_expr| $e)
    elabToTypedRExpr s

  | _ => throwUnsupportedSyntax

mutual
partial def TypedRExpr.toExpr (e : TypedRExpr) : Expr  :=
    let nodeExpr := e.node.toExpr
    let typeExpr := ToExpr.toExpr e.type
    mkAppN (mkConst ``TypedRExpr.mk) #[nodeExpr, typeExpr]


partial def TypedRExprNode.toExpr : TypedRExprNode → Expr
    | .lit n =>
        mkAppN (mkConst ``TypedRExprNode.lit) #[mkNatLit n]
    | .bvar index =>
        mkAppN (mkConst ``TypedRExprNode.bvar) #[mkNatLit index]
    | .fvar name =>
        mkAppN (mkConst ``TypedRExprNode.fvar) #[toExpr name]
    | .const name =>
        mkAppN (mkConst ``TypedRExprNode.const) #[toExpr name]
    | .lam name t body =>
        mkAppN (mkConst ``TypedRExprNode.lam) #[toExpr name, toExpr t, body.toExpr]
    | .ulam name kind body =>
        mkAppN (mkConst ``TypedRExprNode.ulam) #[toExpr name, toExpr kind, body.toExpr]
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

#eval IO.println <| toString [RiseTE| fun a : scalar → scalar => a 10000].node
#check [RiseTE| fun a : scalar → scalar → scalar => a 10000 2]

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


-- def RExpr.bvar2fvar (e : RExpr) (un : Lean.Name) : RExpr :=
--   go un e 0 where
--   go (un : Lean.Name) (e : RExpr) (n : Nat) : RExpr :=
--   match e with
--   | .bvar i => if i == n then .fvar un else e
--   | .fvar .. => e
--   | .const .. => e
--   | .lit .. => e
--   | .app fn arg => .app (go un fn n) (go un arg n)
--   | .lam lun bt b => .lam lun bt (go un b (n+1))
--   | .ulam lun bt b => .ulam lun bt (go un b (n+1))



-- -- -- TODO: translate example programs in shine/src/test/scala/rise/core
-- -- -- /home/n/tub/masters/shine/src/test/scala/apps
-- -- --
-- -- --
-- --
-- --
