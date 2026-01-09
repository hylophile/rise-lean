import Rise

-- shine/src/main/scala/apps/gemmTensor.scala
def tiling2D := [RiseC|
  fun mTile nTile : nat =>
  fun {d : data} =>
  fun {m n : nat} =>
    fun c : m·n·d =>
      c
      |> split (mTile : nat)
      |> map (fun x =>
        x
        |> transpose
        |> split (nTile : nat)
        |> map transpose)
      |> join
]
        -- |> map (fun y => y |> transpose))
#pp tiling2D.type
def tiling2D2 := [RiseC|
  fun mTile nTile : nat =>
  fun {d : data} =>
  fun {m n : nat} =>
    fun c : m·n·d =>
      c
      |> split (mTile : nat)
      |> map (transpose >> split (nTile : nat) >> map transpose)
      |> join
]
        -- |> map (fun y => y |> transpose))
#pp tiling2D2.type

def simpleGemm := [RiseC|
  fun mTileFrag nTileFrag kTileFrag : nat =>
  fun m n k : nat =>
  fun alpha beta a bT c =>
    zip (a |> split (mTileFrag : nat))
        (c |> split (mTileFrag : nat))
    |> map (fun aRowsC => --mapBlock0
      zip (bT |> split (nTileFrag : nat))
          (aRowsC.2 |> transpose |> split (nTileFrag : nat))
      |> map (fun bColumnsTCT =>
        zip (transpose aRowsC.1 |> split (kTileFrag : nat))
            (transpose bColumnsTCT.1 |> split (kTileFrag : nat))
        |> reduceSeq (fun cTile abTiles =>
          -- todo: tensormma
          )
        )
      )

]
