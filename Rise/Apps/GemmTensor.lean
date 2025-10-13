import Rise.Program

-- shine/src/main/scala/apps/gemmTensor.scala
def tiling2D := [RiseC|
  fun mTile nTile : nat =>
    fun c =>
      c |>
      split (mTile) |>
      map (fun x =>
        x |>
        transpose |>
        split(nTile) |>
        map (fun y =>
          y |>
          transpose)) |>
      join
]

#pp tiling2D

#pp tiling2D.type


#pp [RiseC| fun x => mul (fst x) (snd x)]
