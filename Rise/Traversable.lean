import Elevate.Basic
import Rise.Basic

namespace Traversable

-- TODO: check types after rewriting

def TypedRExpr.all (s: Strategy TypedRExpr) : Strategy TypedRExpr :=
  fun expr => match expr.node with
    | .lit _ | .bvar _ | .fvar _ | .const _ | .mvar _ => .ok expr
    | .app f e => do
      let f' <- s f
      let e' <- s e
      return ⟨.app f' e', expr.type⟩
    | .lam bn bt e => do
      let e' <- s e
      return ⟨.lam bn bt e', expr.type⟩
    | .deplam bn bt e => do
      let e' <- s e
      return ⟨.deplam bn bt e', expr.type⟩

def TypedRExpr.some (s: Strategy TypedRExpr) : Strategy TypedRExpr :=
  fun expr => match expr.node with
    | .lit _ | .bvar _ | .fvar _ | .const _ | .mvar _ => .error ""
    | .app f e =>
      match (s f, s e) with
        | (.ok f', .ok e') => .ok ⟨.app f' e', expr.type⟩
        | (.ok f',      _) => .ok ⟨.app f' e , expr.type⟩
        | (_,      .ok e') => .ok ⟨.app f  e', expr.type⟩
        | _ => .error ""
    | .lam bn bt e => (s e).map (⟨.lam bn bt ·, expr.type⟩)
    | .deplam bn bt e => (s e).map (⟨.deplam bn bt ·, expr.type⟩)

def TypedRExpr.one (s: Strategy TypedRExpr) : Strategy TypedRExpr :=
  fun expr => match expr.node with
  | .lit _ | .bvar _ | .fvar _ | .const _ | .mvar _ => .error ""
  | .app f e => match s f with
    | .ok f' => .ok ⟨.app f' e, expr.type⟩
    | _ => (s e).map (⟨.app f ·, expr.type⟩)
  | .lam bn bt e => (s e).map (⟨.lam bn bt ·, expr.type⟩)
  | .deplam bn bt e => (s e).map (⟨.deplam bn bt ·, expr.type⟩)

instance : Traversable TypedRExpr where
  all := TypedRExpr.all
  some := TypedRExpr.some
  one := TypedRExpr.one
