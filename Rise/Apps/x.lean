import Rise.Program 

def prodMult := [RiseC| fun {d : data} => fun xs : d × d => xs.1 * xs.2]
-- #pp prodMult.type

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduce add 0.0f32
]
-- #pp dot.type

