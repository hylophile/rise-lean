import Rise
-- from shine/src/test/scala/apps/scal.scala


-- def simpleScal := [RiseC|
--   fun n : nat =>
--   fun input : n·f32 =>
--   fun alpha : f32 =>
--     input |> mapSeq (fun x => alpha * x)
-- ]

set_option egg.debug_enable true in
def scalIntel := [RiseC|
  fun n : nat =>
  fun input : n·f32 =>
  fun alpha : f32 =>
    input |>
    split (4 * 128 * 128 : nat) |>
    mapPar(
      asVectorAligned 4 >>
      split 128 >>
      mapSeq(mapSeq(fun x =>
        vectorFromScalar alpha |> mul x
      )) >> join >> asScalar
    ) |>
    join
]
#pp scalIntel

-- def scalt := [RiseC|
--   fun n : nat =>
--   fun input : n·f32 =>
--   fun alpha : f32 =>
--     input |>
--     split (4 * 128 * 128 : nat) |>
--     split 2 |>

--     join
-- ]
-- #pp scalt.type
