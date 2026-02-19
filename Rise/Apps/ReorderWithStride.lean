import Rise
-- val reorderWithStride: ToBeTyped[Expr] = {
--   depFun((s: Nat) => {
--     impl { n: Nat =>
--       def f = n2nFun(n)(i => (i / (n /^ s)) + (s * (i % (n /^ s))))
--       reorder(n)(f)(f)
--     }
--   })
-- }

def reorderWithStride := [RiseC|
fun s : nat =>
  reorder s (i ↦ i * 2)-- (i ↦ i*6)
]

#pp reorderWithStride

def liftex :=[RiseC|
fun n:nat => fun matrix : n··(i ↦ i+1·f32) =>
fun vec : n·f32 => matrix
  |> map (fun idx : nat => fun row =>
  let v := take (idx+1) vec in
  zip row v |> map mul |> reduce add 0.0f32)
]
