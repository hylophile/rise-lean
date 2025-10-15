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
-- #pp gemvHighLevel.type


-- fuel runs out here. probably a bug?
-- #pp [RiseC| fun x => add x (x.2.1)]
#pp [RiseC| (generate (fun dummy : idx[64] => 0.0f32))]

def gemvBlastN := [RiseC|
  fun (n m : nat) =>
  fun mat : m·n·f32 =>
  fun xs : n·f32 =>
  fun ys : m·f32 =>
  fun alpha beta =>
    join << map (fun matChunk =>
      (fun y => map (fun x => x.1 * alpha + x.2 * beta) <| zip y (map snd matChunk))
      <<
      reduceSeq (fun acc next  =>
        map (fun x =>
          reduceSeq (fun acc2 next2 => acc2 + next2.1 * next2.2)
                    x.1
                    <| zip x.2 (map id next.2)
        ) <| zip acc next.1
      )
      (map id (generate (fun dummy : idx[64] => 0.0f32)))
      <| zip (transpose << map (split (64 : nat) << fst) <| matChunk) (split (64 : nat) xs)
      ) << split (64 : nat) <| zip mat ys
]
#pp gemvBlastN.type

def gemvFused := [RiseC|
  fun (n m : nat) =>
  fun mat : m·n·f32 =>
  fun xs : n·f32 =>
  fun ys : m·f32 =>
  fun alpha beta =>
    zip mat ys
    |> map -- mapWorkGroup
      (fun t =>
        zip xs t.1
        |> split (n : nat)
        |> map -- toLocalFun mapLocal oclReduceSeq
          (reduceSeq (fun a x => (x.1 * x.2) + a) 0.0f32)
        |> map
          (fun y => (alpha * y) + (t.2 * beta))
      )
    |> join
]
#pp gemvFused.type

-- gemvFusedAMD needs reorderWithStride, which has nat2nat fun
