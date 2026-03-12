import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing

def simpleScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun x => alpha * x)
 ]

def applyInferAccess := inferAccess simpleScal

#pp simpleScal
#eval applyInferAccess


def complexScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun input => alpha * input)
 ]

#pp complexScal
