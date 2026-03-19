import DPIA.InferAccessAnnotation
import Rise
import DPIA.FromRise
import DPIA.Printing

def prodMult := [RiseC| fun d : data => fun xs : d × d => xs.1 * xs.2]
#pp prodMult

#eval inferAccess prodMult

def foo := [RiseC| fun y : f32 => (fun x : f32 =>  x * y) y ]
#pp foo

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq ($prodMult f32)|> toMem |> reduceSeq add 0.0f32
]

def simpleZip := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq ($prodMult f32)
]

def applyInferAccessToDot := inferAccess dot

#pp dot
#pp fromRise dot

#pp simpleZip
#pp fromRise simpleZip
#pp inferAccess simpleZip
#pp fromRise dot
