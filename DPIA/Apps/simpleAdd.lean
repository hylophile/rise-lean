import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing

def add := [RiseC|
  fun x :  f32 =>
    fun y : f32 =>
        (fun x : f32 => x + y + x )(x)
]

def add2 := [RiseC|
  fun x :  f32 =>
    (fun x : f32 => x + x )(x)
]

#pp add
#eval inferAccess add
#eval add2
#pp inferAccess add
