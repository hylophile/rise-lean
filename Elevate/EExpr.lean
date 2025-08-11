import Lean
import Elevate.Prelude

mutual
structure EExpr (P: Type) where
    e: EExpr.Node P
    s: Lean.Syntax

inductive EExpr.Node (P: Type) where
    | rule (s: Strategy P)
    | skip
    | abort
    | seq (s1 s2: EExpr P)
    | lchoice (s1 s2: EExpr P)
    | one (s: EExpr P)
    | some (s: EExpr P)
    | all (s: EExpr P)
end
