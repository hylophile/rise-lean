import DPIA.InferAccessAnnotation
import Rise

def prodMult := [RiseC| fun d : data => fun xs : d × d => xs.1 * xs.2]
#pp prodMult

#eval inferAccess prodMult

def foo := [RiseC| fun y : f32 => (fun x : f32 =>  x * y) y ]
#pp foo

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq ($prodMult (f32 : data)) |> reduceSeq add 0.0f32
]
#pp dot
#eval inferAccess dot
