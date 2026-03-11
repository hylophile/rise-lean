import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing

def simpleScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun x => alpha * x)
 ]

def firstElem :=  let first := (inferAccess simpleScal).toList.head?
                  match first with
                    | some y => y
                    | none => ({node:= .bvar 0 (Lean.Name.mkSimple "failed"), type := (.data .natType) : TypedRExpr}, PhraseType.comm)

#pp simpleScal
#eval inferAccess simpleScal
#eval firstElem
#pp printList (inferAccess simpleScal).toList

def complexScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun input => alpha * input)
 ]

#pp complexScal
#pp printList (inferAccess complexScal).toList
