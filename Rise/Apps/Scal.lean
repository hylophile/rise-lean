import Rise.Program
-- from shine/src/test/scala/apps/scal.scala


def simpleScal := [RiseC|
  fun n : nat =>
  fun input : n·f32 =>
  fun alpha : f32 =>
    input |> mapSeq (fun x => alpha * x)
]

def scalIntel := [RiseC|
  fun n : nat =>
  fun input : n·f32 =>
  fun alpha : f32 =>
    input |>
    split (4 * 128 * 128 : nat) |>
    mapPar(
      asVectorAligned (4 : nat) >>
      split (128 : nat) >>
      mapSeq(mapSeq(fun x =>
        vectorFromScalar alpha |> mul x
      )) >> join >> asScalar
    ) |>
    join
]
#pp scalIntel.type

def scalt := [RiseC|
  fun n : nat =>
  fun input : n·f32 =>
  fun alpha : f32 =>
    input |>
    split (4 * 128 * 128 : nat) |>
    split (2 : nat) |>
    
    join
]
#pp scalt.type
