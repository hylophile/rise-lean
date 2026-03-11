import DPIA.InferAccessAnnotation
import Rise

def add := [RiseC|
  fun x :  f32 =>
    fun y : f32 =>
        (fun x : f32 => x + y + x )(x)
]

#pp add
#eval inferAccess add
