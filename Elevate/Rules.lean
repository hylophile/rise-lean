import Rise.Basic
import Rise.Program
import Rise.Traversable
import Elevate.Basic

import Lean
open Lean Elab Command

def rule.transpose_transpose : Strategy TypedRExpr
  -- fun e => match e.node with
  | ⟨.app ⟨.const `transpose, _⟩ ⟨.app ⟨.const `transpose, _⟩ x, _⟩, _⟩ =>
    .ok x
  | _ => .error "rule.transpose_transpose"

-- -- rule transpose_transpose :=
-- --   .app (.const `transpose) (.app (.const `transpose) x) =>
-- --     .ok x

-- -- rule transpose_transpose :=
-- --   transpose transpose ?x ~> ?x

-- declare_syntax_cat elevate_rule
-- syntax ident ":=" rise_expr "~>" rise_expr : elevate_rule

-- macro_rules
--   | `(elevate_rule| $n:ident := $e1:rise_expr ~> $e2:rise_expr) =>
--       `(def x := 3)

-- -- def x: NameLit := _
-- elab "#rule" n:ident ":=" e1:rise_expr "~>" e2:rise_expr : command => do
--       -- let name : TSyntax `ident := n.getId.append `rule
--       elabCommand (← `(def $n : Strategy Rise.Basic.TypedExpr := 3))


-- #rule xyz := transpose transpose ?x ~> ?x

-- elab "#rule" n:ident ":=" e1:term "~>" e:term : command => do
--   -- let e1 ← elabToTypedRExpr e1
--   -- let rhs ← compileRiseRHS e2 ctx
--   let lhs ← liftTermElabM <| Term.elabTerm e1 none
--   let lhs := `(⟨.app ⟨.const `transpose, _⟩ ⟨.app ⟨.const `transpose, _⟩ x, _⟩, _⟩)
--   let rhs ← liftTermElabM <| Term.elabTerm e none
--   let errMsg := Lean.mkStrLit s!"rule {n.getId}"
--   elabCommand (← `(def $n : Strategy Rise.Basic.TypedExpr :=
--     fun e => match e with
--       | $lhs => .ok $rhs
--       | _    => .error $errMsg))

-- #eval x

-- elab "[Elevate|" "rule" n:ident ":=" e1:rise_expr "~>" e2:rise_expr "]" : command => do
  -- let defName := n.getId
  -- let typeStx := type
  -- let valueStx := e1

  -- -- Elaborate the type and value
  -- let typeExpr ← liftTermElabM (Term.elabType typeStx)
  -- let valueExpr ← liftTermElabM (Term.elabTermEnsuringType valueStx typeExpr)

  -- -- Create the definition
  -- let defInfo : DefinitionVal := {
  --   name := defName
  --   levelParams := []
  --   type := typeExpr
  --   value := valueExpr
  --   -- hints := ReducibilityHints.regular (getReducibleHeight (← getEnv) valueExpr)
  --   safety := DefinitionSafety.safe
  -- }

  -- addDecl (Declaration.defnDecl defInfo)
  -- elabCommand `(#eval def x := 3)

-- #eval [Elevate| rule xx := transpose transpose ?x ~> x]

#eval [RiseTE| ?x]

#eval
let input := [RiseC|
  fun (x : 32·32·f32) => transpose (transpose x) ];

let expected := [RiseC|
  fun (x : 32·32·f32) => x ];

match (Strategy.topDown rule.transpose_transpose) input with
  | .ok computed =>
    computed == expected
  | .error _ => false
