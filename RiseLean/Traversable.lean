import Elevate.Prelude
import RiseLean.Prelude

namespace Traversable

def RExpr.all (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ | .fvar _ | .const _ => .ok e
    | .app f e => do
      let f' <- s f
      let e' <- s e
      return (.app f' e')
    | .lam bn bt e => do
      let e' <- s e
      return (.lam bn bt e')
    | .ulam bn bt e => do
      let e' <- s e
      return (.ulam bn bt e')

def RExpr.some (s: Strategy RExpr) : Strategy RExpr
  | .lit _ | .bvar _ | .fvar _ | .const _ => .error ""
  | .app f e =>
    match (s f, s e) with
      | (.ok f', .ok e') => .ok (.app f' e')
      | (.ok f',      _) => .ok (.app f' e )
      | (_,      .ok e') => .ok (.app f  e')
      | _ => .error ""
  | .lam bn bt e => (s e).map (.lam bn bt ·)
  | .ulam bn bt e => (s e).map (.ulam bn bt ·)

def RExpr.one (s: Strategy RExpr) : Strategy RExpr
  | .lit _ | .bvar _ | .fvar _ | .const _ => .error ""
  | .app f e => match s f with
    | .ok f' => .ok (.app f' e)
    | _ => (s e).map (.app f ·)
  | .lam bn bt e => (s e).map (.lam bn bt ·)
  | .ulam bn bt e => (s e).map (.ulam bn bt ·)

instance : Traversable RExpr where
  all := RExpr.all
  some := RExpr.some
  one := RExpr.one
