import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing

def simpleScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun x => alpha * x)
 ]


#pp simpleScal
#eval inferAccess simpleScal


def complexScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun input => alpha * input)
 ]

#pp complexScal
