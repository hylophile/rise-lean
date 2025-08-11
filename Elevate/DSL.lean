import Elevate.Prelude

open Lean Elab Meta

declare_syntax_cat elevate_expr
syntax term                               : elevate_expr
syntax elevate_expr " ; " elevate_expr    : elevate_expr
syntax elevate_expr " <+ " elevate_expr   : elevate_expr
syntax "[Elevate|" elevate_expr "]"       : term

macro_rules
  | `([Elevate| $t:term ]) => `($t)
  | `([Elevate| $t1:elevate_expr ; $t2:elevate_expr ]) =>
    `(Strategy.seq [Elevate|$t1] [Elevate|$t2])
  | `([Elevate| $t1:elevate_expr <+ $t2:elevate_expr ]) =>
    `(Strategy.leftChoice [Elevate|$t1] [Elevate|$t2])

example : Strategy P :=
  [Elevate|
    Strategy.id ; Strategy.id <+ Strategy.fail
  ]
