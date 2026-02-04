import Rise

def prodMult := [RiseC| fun {d : data} => fun xs : d × d => xs.1 * xs.2]
-- #pp prodMult.type

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduce add 0.0f32
]
-- #pp dot.type


-- def x := [RiseC|
-- fun a b : nat =>
-- fun {m : nat} =>
-- fun xs : m·f32 =>
-- concat (split (a+b : nat) xs) (split (a-b : nat) xs)
-- ]
-- #pp x.type


-- def y := [RiseC|
--   fun a b : nat =>
--   fun {q : nat} =>
--   fun xs : q·f32 =>
--   add (split (a+b : nat) xs)
--       (split (a-b : nat) xs)
-- ]
-- #pp y.type

-- todo: fuel runs out here. probably a bug
-- #pp [RiseC| fun x => add x (x.2.1)]
-- 
-- #pp [RiseC| (generate (fun dummy : idx[64] => 0.0f32))]

def y := [RiseC|

  fun a b : nat =>
  fun {p q : nat} =>
  fun xs : p·f32 =>
  fun ys : q·f32 =>
  take 5 <| add xs ys
]
#pp y.type
-- def y := [RiseC|

--   fun a b : nat =>
--   fun {q : nat} =>
--   fun xs : q·f32 =>
--   add (take a xs)
--       (take b xs)
-- ]
-- #pp y.type

-- def z := [RiseC|
--   fun a b : nat =>
--   fun {q : nat} =>
--   fun xs : q·f32 =>
--   fun ys : 5·f32 =>
--   add (xs) (ys)
-- ]
-- #pp z.type
