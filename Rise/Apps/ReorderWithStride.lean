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
  reorder s (i ↦ i * 2) (i ↦ i*6)
]

#pp reorderWithStride
