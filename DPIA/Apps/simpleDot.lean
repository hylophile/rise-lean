import DPIA.InferAccessAnnotation
import Rise
import DPIA.FromRise
import DPIA.Compilation.generator
import DPIA.betaReduction

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
#pp inferAccess dot
#pp reduction (fromRise dot)

#pp simpleZip
#pp fromRise simpleZip
#pp inferAccess simpleZip
#pp fromRise dot

def fRSimpleZip := fromRise simpleZip
#pp fRSimpleZip
#pp applyToImp fRSimpleZip
#pp reduction fRSimpleZip

def fRDot := fromRise dot
#pp applyToImp fRDot

def TIDot := (applyToImp fRDot)[0]
#pp TIDot.node

def newVal := match TIDot.node with
               | .imperative (.new _ f) => f
               | _ => TIDot

def vals := match newVal.node with
              | .pair p1 p2 => [p1,p2]
              | _ => [newVal]

#pp vals

def tISimpleZip := applyToImp fRSimpleZip
def body := generateCode tISimpleZip

#pp tISimpleZip
#pp body
#pp makeCModule body tISimpleZip.dropLast

def tIDot := applyToImp fRDot
def bodyDot := generateCode tIDot

#pp fRDot
#pp tIDot
#eval bodyDot
#pp makeCModule bodyDot tIDot.dropLast
