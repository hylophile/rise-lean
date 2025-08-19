import Lean
open Lean
open Lean.Meta
open Lean.Elab
--open Elab.Term
syntax "mimi" : term
-- A simple example to construct a match expression

inductive X
  | p (s: String)
  | y
  | z (n: Name) (n : Nat)
  | n

macro_rules
  | `(mimi) => do
  let x ← `(0)
  let q ← `(.z `ny meow)
  let discr ← `(n)
  let meowName : Name := `meow
  let q <- `(.z `ny $(mkIdent meowName))

  let matchExpr ← `(fun x =>
    match x with
    | .p s => "no"
    | .y => "yes"
    | $q => "interesting"
    | _ => "maybe"
  )
  return matchExpr

  #eval mimi <| X.z `ny 3

--namespace rule
--end rule

open Command
elab "#rule " name:ident : command => do
    let ruleName := name.getId
    let defName := Name.mkStr2 "rule" ruleName.toString
    let ruleIdent := mkIdent defName
    let defStx : TSyntax `command <- `(def $(mkIdent defName) : String := "default rule")
    logInfo defStx
    elabCommand defStx.raw
  

-- Example usage:
#rule myRule

-- This generates: def rule.myRule : String := "default rule"

#eval rule.myRule -- Should show: rule.myRule : String
open rule
#check myRule
