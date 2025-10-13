import Rise.Program
-- /shine/src/main/scala/apps/gemv.scala
--


def prodMult := [RiseC| fun {d : data} => fun xs : d × d => mul (fst xs) (snd xs)]
-- #pp prodMult.type


def scale := [RiseC|
  fun {n : nat} =>
  fun xs : n·f32 =>
  fun a : f32 =>
    map (fun x => mul a x) xs
]
-- #pp scale.type

def scaleSeq := [RiseC|
  fun {n : nat} =>
  fun xs : n·f32 =>
  fun a : f32 =>
    mapSeq (fun x => mul a x) xs
]

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduce add 0.0f32 
]
-- #pp dot.type


def gemvHighLevel := [RiseC|
  fun {n m : nat} =>
  fun mat : m·n·f32 =>
  fun xs ys alpha beta =>
    zip (map (fun row => mul alpha ($dot row xs)) mat)
        ($scale ys beta)
    |>
    map (fun x => add (fst x) (snd x))
]
#pp gemvHighLevel.type


def gemvFused := [RiseC|
  fun (n m : nat) =>
  fun mat : m·n·f32 =>
  fun xs : n·f32 =>
  fun ys : m·f32 =>
  fun alpha beta =>
    zip mat ys
    |> map -- mapWorkGroup
      (fun t =>
        zip xs (fst t)
        |> split n
        |> map
          (reduceSeq (fun a x => add (mul (fst x) (snd x)) a) 0.0f32)
        |> map
          (fun y => add (mul alpha y) (mul (snd t) beta))
      )
    |> join
]
#pp gemvFused.type

-- #pp [RiseC|
--   fun (n m : nat) =>
--   fun mat : m·n·f32 =>
--   fun xs : n·f32 =>
--   fun ys : m·f32 =>
--   fun alpha beta =>
--     -- zip mat ys
--     -- |> map -- mapWorkGroup
--       (fun t =>
--         zip xs (fst t)
--         |> split n
--         |> map
--           (reduceSeq (fun a x => add (mul (fst x) (snd x)) a) 0.0f32)
--         |> map
--           (fun y => add (mul alpha y) (mul (snd t) beta))
--       )
--     -- |> join
-- ]

-- #pp [RiseC|
--   fun (n m : nat) =>
--   fun mat : m·n·f32 =>
--   fun xs : n·f32 =>
--   fun ys : m·f32 =>
--   fun alpha beta =>
--     -- zip mat ys
--     -- |> map -- mapWorkGroup
--       (fun t : n·f32 × f32 =>
--         zip xs (fst t)
--         |> split n
--         -- |> map
--         --   (reduceSeq (fun a x => add (mul (fst x) (snd x)) a) 0.0f32)
--         -- |> map
--         --   (fun y => add (mul alpha y) (mul (snd t) beta))
--       )
--     -- |> join
-- ]

-- #pp [RiseC|
-- fun a : nat =>
-- fun b : nat =>
-- fun xs : b·f32 =>
-- split a xs]
