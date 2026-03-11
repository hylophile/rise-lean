import DPIA.InferAccessAnnotation

def printList (list : List (RExpr × PhraseType)) : String :=
  match list with
    | [] => ""
    | (k, x) :: ys => s!"{k} \n type: {x} \n\n" ++ printList ys
