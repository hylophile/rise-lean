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



-- λ(e1 : exp[f32, read]) =>
--   λ(e2 : exp[f32, read]) =>
--     λ(e3 : exp[f32, read]) =>
--       ((λ(x16 : exp[f32, read]).
--           λ(x17 : exp[f32, read]) => BinOp(+,(x16 : exp[f32, read]),(x17 : exp[f32, read]))
--             ((λ(x18 : exp[f32, read]) =>
--               λ(x19 : exp[f32, read]) => BinOp(+,(x18 : exp[f32, read]),(x19 : exp[f32, read]))
--               ((λ(x20 : exp[f32, read]) =>
--                   λ(x21 : exp[f32, read]) => BinOp(+,(x20 : exp[f32, read]),(x21 : exp[f32, read])) (e1 : exp[f32, read])) (e2 : exp[f32, read]))) (e3 : exp[f32, read]))) Literal(0.0f))
