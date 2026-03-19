import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing
import DPIA.FromRise

def add := [RiseC|
  fun x :  f32 =>
    fun y : f32 =>
        fun z : f32 => x + y + z + 0.0f32
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

#pp inferAccess add
#pp addAndApply
#pp inferAccess addAndApply
#eval add2
#pp inferAccess addAndApply
#pp fromRise add
