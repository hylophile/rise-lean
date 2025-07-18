I'm trying to write a DSL that has binders, but uses Lean's binders to represent them. I followed the [PHOAS example](https://docs.lean-lang.org/lean4/doc/examples/phoas.lean.html) and am now trying to add an elaborator, but struggling with that.

The first issue is that "result contains metavariables". It seems that `?rep` is a metavariable in the first `#reduce`. I think what I want to do here is add `rep` as an implicit argument, but I don't know how.

The second issue is that I don't know how to actually "use" the bound variable when elaborating identifiers. (See comment.)

Also, if there's a better technique to define a DSL which uses Lean's binders, I'm all ears!

```
import Lean
open Lean Elab Command Term Meta

inductive LambType where
  | nat
  | fn : LambType → LambType → LambType

inductive LambTerm' (rep : LambType → Type) : LambType → Type
  | var   : rep ty → LambTerm' rep ty
  | const : Nat → LambTerm' rep .nat
  | abst   : (rep dom → LambTerm' rep ran) → LambTerm' rep (.fn dom ran)

def LambTerm (ty : LambType) := {rep : LambType → Type} → LambTerm' rep ty

def identity : LambTerm (.fn .nat .nat) :=
  .abst (fun x => .var x)

declare_syntax_cat                  lamb_expr
syntax "lamb" ident "." lamb_expr : lamb_expr
syntax ident                      : lamb_expr
syntax num                        : lamb_expr

partial def elabLamb : Syntax → TermElabM Expr
  | `(lamb_expr| $x:ident) => do
    -- just a placeholder. how do i "use" the bound variable
    -- that was created by the lamb $x:ident . $b:lamb_expr elaboration?
    mkAppM ``LambTerm'.const #[mkNatLit 1]
  | `(lamb_expr| lamb $x:ident . $b:lamb_expr) => do
    let type ← mkFreshTypeMVar
    withLocalDeclD x.getId type fun fvar => do
      let b ← elabLamb b
      let abst ← mkLambdaFVars #[fvar] b
      mkAppM ``LambTerm'.abst #[abst]
  | `(lamb_expr| $n:num) =>
    mkAppM ``LambTerm'.const #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "test_elabLamb " l:lamb_expr : term => elabLamb l

set_option pp.explicit true

-- AppBuilder for 'mkAppM', result contains metavariables
--   @LambTerm'.const ?rep (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
#reduce test_elabLamb 3

-- AppBuilder for 'mkAppM', result contains metavariables
--   @LambTerm'.const ?rep (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
#reduce test_elabLamb lamb x . x
```
