import Rise
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
        fun z : f32 => x + y + z
]

def add2 := [RiseC|
  fun x :  f32 =>
    (fun x : f32 => x + x )(x)
]

def fRAdd := fromRise add

#pp inferAccess add
#pp addAndApply
#pp inferAccess addAndApply
#pp fromRise addAndApply
#pp reduction (fromRise addAndApply)
#eval add2
#pp inferAccess addAndApply
#pp fromRise add

#pp reduction fRAdd
def tIAdd := applyToImp fRAdd
#pp tIAdd.getLast?

def body := generateCode tIAdd
#pp body

#pp makeCModule body tIAdd.dropLast

def fRAdd2 := fromRise add2
def tIAdd2 := applyToImp fRAdd2
def body2 := generateCode tIAdd2

#pp tIAdd2

#pp body2
#pp makeCModule body2 tIAdd2.dropLast

#pp CCodeFromRise add
