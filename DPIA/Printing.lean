import DPIA.InferAccessAnnotation

def printList (list : List (TypedRExpr × PhraseType)) : String :=
  match list with
    | [] => ""
    | (k, x) :: ys => s!"{k} \n type: {x} \n\n" ++ printList ys
