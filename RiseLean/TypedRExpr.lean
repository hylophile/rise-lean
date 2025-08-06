import RiseLean.Prelude
import RiseLean.RElabM
import RiseLean.Expr
import RiseLean.Type
import Lean
open Lean Elab

mutual
structure TypedRExpr where
  node: TypedRExprNode
  type: RType

inductive TypedRExprNode where
  | bvar (deBruijnIndex : Nat)
  | fvar (userName : Lean.Name) -- this is a problem when multiple idents have the same name?
-- mvar
  | const (userName : Lean.Name)
  | lit (val : Nat)
  | app (fn arg : TypedRExpr)
  | lam (binderName : Lean.Name) (binderType : RType) (body : TypedRExpr)
  | ulam (binderName : Lean.Name) (binderKind : RKind) (body : TypedRExpr)
end

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

#check [RiseTE| fun a : scalar → scalar => a 10000]
#check [RiseTE| fun a : scalar → scalar → scalar => a 10000 2]
