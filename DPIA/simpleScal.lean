import DPIA.inferAccessAnnotation
import Rise

def simpleScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun x => alpha * x)
 ]

#eval inferAccess simpleScal
