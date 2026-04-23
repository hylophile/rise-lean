import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing
import DPIA.FromRise
import DPIA.Compilation.generator

def simpleScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun x => alpha * x)
 ]

def applyInferAccess := inferAccess simpleScal

#pp simpleScal
#eval applyInferAccess
#pp applyInferAccess
#pp fromRise simpleScal

def fRSimpleScal := fromRise simpleScal
#pp fRSimpleScal
#pp uniqueRenaming fRSimpleScal
#pp applyToImp fRSimpleScal

def tISimpleScal := applyToImp fRSimpleScal
def body := generateCode tISimpleScal

#pp tISimpleScal
#pp body
#pp makeCModule body tISimpleScal.dropLast


def complexScal := [RiseC|
   fun n : nat =>
   fun input : n·f32 =>
   fun alpha : f32 =>
     input |> mapSeq (fun input => alpha * input)
 ]

#pp fromRise complexScal

#pp fromRise complexScal

#pp uniqueRenaming (fromRise complexScal)
