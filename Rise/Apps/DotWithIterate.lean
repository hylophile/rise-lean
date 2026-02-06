import Rise

def prodMult := [RiseC| fun d : data => fun xs : d × d => xs.1 * xs.2]
#pp prodMult

#eval prodMult

def foo := [RiseC| fun y : f32 => (fun x : f32 =>  x * y) y ]
#pp foo

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map ($prodMult (f32 : data)) |> reduce add 0.0f32
]
#pp dot

def dot3 := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq $prodMult |> toMem |> reduceSeq add 0.0f32
]
#pp dot3

def dot4 := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     reduceSeq add 0.0f32 (
        toMem (
          mapSeq $prodMult (zip as bs)
        )
      )
]
#pp dot4.type

#eval prodMult
def dot2 := [RiseC|
  fun {n : nat} =>
  fun input : n·f32 =>
  input
  |> split (128 : nat)
  |> map (split (2 : nat)
      >> map (reduceSeq add 0.0f32)
      >> oclIterate (6 : nat) (fun dummy : nat => split (2 : nat) >> map (reduce add 0.0f32)))
  |> join
]
#pp dot2

-- #pp [RiseC|
--       oclIterate (6 : nat) (fun dummy : nat => split (2 : nat) >> map (reduce add 0.0f32))
-- ].type
-- #pp [RiseC|
--   fun xs:16·f32 =>
--   iterate (fun dummy : nat => split (2 : nat) >> map (reduce add 0.0f32)) xs
-- ].type
-- #pp [RiseC|
--   split (2 : nat) >> map (reduce add 0.0f32)
-- ].type
