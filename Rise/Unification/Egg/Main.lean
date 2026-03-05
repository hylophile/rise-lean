import Rise.Unification.Egg.Run
import Rise.Unification.Egg.Parse
import Rise.Unification.MVars


def RNat.toEggSExpr : RNat → String
  | .bvar idx name => s!"(nat_bvar {sane name}_{idx})"
  | .mvar id name => s!"(nat_mvar {sane name}_{id})"
  | .nat n => s!"{n}"
  | .plus n m => s!"(+ {n.toEggSExpr} {m.toEggSExpr})"
  | .minus n m => s!"(- {n.toEggSExpr} {m.toEggSExpr})"
  | .mult n m => s!"(* {n.toEggSExpr} {m.toEggSExpr})"
  | .div n m => s!"(/ {n.toEggSExpr} {m.toEggSExpr})"
  | .pow n m => s!"(^ {n.toEggSExpr} {m.toEggSExpr})"

def RData.toEggSExpr : RData → String
  | .bvar idx name => s!"(data_bvar {sane name}_{idx})"
  | .mvar id name  => s!"(data_mvar {sane name}_{id})"
  | .array n d     => s!"(array {n.toEggSExpr} {d.toEggSExpr})"
  | .pair d1 d2    => s!"(pair {d1.toEggSExpr} {d2.toEggSExpr})"
  | .index n       => s!"(index {n.toEggSExpr})"
  | .scalar x      => s!"{x}"
  | .natType       => "natType"
  | .vector n d    => s!"(vector {n.toEggSExpr} {d.toEggSExpr})"

def RType.toEggSExpr : RType → String
  | .data dt => dt.toEggSExpr
  | .pi kind _pc un body => s!"(pi {un} {kind} {body.toEggSExpr})"
  | .fn binderType body => s!"(-> {binderType.toEggSExpr} {body.toEggSExpr})"
