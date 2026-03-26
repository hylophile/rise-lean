import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing
import DPIA.FromRise
import DPIA.Compilation.TranslationToImperative
import DPIA.Compilation.generator

def add := [RiseC|
  fun m :  f32 =>
    fun n : f32 =>
        fun o : f32 => m + n + o + 0.0f32
]

def add1 := [RiseC|
  fun x :  f32 => x + 0.0f32
]

def addAndApply := [RiseC|
  fun x :  f32 =>
    fun y : f32 =>
        (fun x : f32 => x + y + x )(x)
]

def add2 := [RiseC|
  fun x :  f32 =>
    (fun x : f32 => x + x )(x)
]

def fRAdd := fromRise add

#pp inferAccess add
#pp addAndApply
#pp inferAccess addAndApply
#eval add2
#pp inferAccess addAndApply
#pp fromRise add

#pp applyToImp fRAdd
