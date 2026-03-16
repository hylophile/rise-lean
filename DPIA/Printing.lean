import DPIA.InferAccessAnnotation

def printList (list : List (RExpr × PhraseType)) : String :=
  match list with
    | [] => ""
    | (k, x) :: ys => s!"{k} \n type: {x} \n\n" ++ printList ys

private def indent (s : String) : String :=
  s.trimAscii |>.split '\n' |>.toStringList |>.map (λ s => "  " ++ s) |> String.intercalate "\n"

partial def printRExprNodePt (expr : RExprPt) : String :=
  let exprStr := toString expr
  match expr.node with
    | .bvar ..    => exprStr ++ "\n\n"
    | .const _      => exprStr ++ "\n\n"
    | .lit _        => exprStr ++ "\n\n"
    | .app f e      => exprStr ++ "\n\n" ++ printRExprNodePt f ++ "\n\n" ++ printRExprNodePt e ++ "\n\n"
    | .depapp f _   => exprStr ++ "\n\n" ++ printRExprNodePt f ++ "\n\n"
    | .lam _ _ b    => exprStr ++ "\n\n" ++ printRExprNodePt b ++ "\n\n"
    | .deplam _ _ b => exprStr ++ "\n\n" ++ printRExprNodePt b ++ "\n\n"

partial def printPt (expr : RExprPt) : String :=
  "\n\n\n" ++ printRExprNodePt expr
