import DPIA.InferAccessAnnotation
import Rise
import DPIA.Printing

def add := [RiseC|
  fun x :  f32 =>
    fun y : f32 =>
        (fun x : f32 => x + y + x )(x)
]

#pp add
#eval inferAccess add
#pp printList (inferAccess add).toList
