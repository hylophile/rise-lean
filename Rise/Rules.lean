import Rise.Prelude
import Rise.Program
import Rise.Traversable
import Elevate.Prelude

def rule.transpose_transpose : Strategy TypedRExpr
  -- fun e => match e.node with
  | ⟨.app ⟨.const `transpose, _⟩ ⟨.app ⟨.const `transpose, _⟩ x, _⟩, _⟩ =>
    .ok x
  | _ => .error "rule.transpose_transpose"

-- rule transpose_transpose :=
--   .app (.const `transpose) (.app (.const `transpose) x) =>
--     .ok x

#eval
let input := [RiseC|
  fun (x : 32·32·scalar) => transpose (transpose x) ];

let expected := [RiseC|
  fun (x : 32·32·scalar) => x ];

match (Strategy.topDown rule.transpose_transpose) input with
  | .ok computed =>
    computed == expected
  | .error _ => false
