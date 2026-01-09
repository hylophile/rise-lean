import Rise
-- /shine/src/main/scala/apps/mm.scala

def prodMult := [RiseC| fun {d : data} => fun xs : d × d => xs.1 * xs.2]
-- #pp prodMult.type

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduce add 0.0f32
]
-- #pp dot.type
def dotSeq := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduceSeq add 0.0f32
]
-- #pp dot.type

def mmHighLevel := [RiseC|
  fun {n m p : nat} =>
  fun a : m·n·f32 =>
  fun b : n·p·f32 =>
    a |> map (fun aRow =>
      transpose b |> map (fun bCol => $dot aRow bCol)
    )
]
#pp mmHighLevel.type


def x := [RiseC|
  fun x : f32 => id 3

]
#pp x.type
