import Rise.Program
-- /shine/src/main/scala/apps/gemv.scala
--


def prodMult := [RiseC| fun {d : data} => fun xs : d × d => mul (fst xs) (snd xs)]
#pp prodMult.type


def scale := [RiseC|
  fun {n : nat} =>
  fun xs : n·f32 =>
  fun a : f32 =>
    map (fun x => mul a x) xs
]
#pp scale.type

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
#pp dot.type


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


def gemvFused :=[RiseC|
  fun {n m : nat} =>
  fun mat : m·n·f32 =>
  fun xs ys alpha beta =>
    zip mat ys
    |> map -- mapWorkGroup
      (fun t =>
        zip xs (fst t)
        |> split n
        |> map
          (reduceSeq (fun a => fun x => add ($prodMult x) a) 0.0f32)
        |> map
          (fun x => add (mul alpha x) (mul (snd t) beta))
      )
    |> join
]
