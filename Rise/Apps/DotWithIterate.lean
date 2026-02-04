import Rise

def prodMult := [RiseC| fun {d : data} => fun xs : d × d => xs.1 * xs.2]
#pp prodMult.type

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> (reduce add) 0.0f32
]
#pp dot.type

def dot2 := [RiseC|
  fun {n : nat} =>
  fun input : n·f32 =>
  input
  |> split 128
  |> map (split 2
      >> map (reduceSeq add 0.0f32)
      >> oclIterate 6 (fun dummy : nat => split 2 >> map (reduce add 0.0f32)))
  |> join
]
#pp dot2

-- #pp [RiseC|
--       oclIterate 6 (fun dummy : nat => split 2 >> map (reduce add 0.0f32))
-- ].type
-- #pp [RiseC|
--   fun xs:16·f32 =>
--   iterate (fun dummy : nat => split 2 >> map (reduce add 0.0f32)) xs
-- ].type
-- #pp [RiseC|
--   split 2 >> map (reduce add 0.0f32)
-- ].type
