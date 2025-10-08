import Rise.Program
open Lean

-------------------------------------------------------------------------


-- #pp [RiseC|
--   fun as => fun bs =>
--        zip as bs |> map (fun ab => mul (fst ab) (snd ab)) |> reduce add 0
-- ]


--  #pp [RiseC|
--    fun(k : nat) => fun(a : k·f32) => reduce add 0.0f32 a
--  ]


-- #pp [RiseC|
--   fun x:2·3·f32 => concat (x |> transpose |> join) (x |> join)
-- ]

-- #eval [RiseC|
--   take
-- ]

-- #pp [RiseC|
--   circularBuffer
-- ]

-- #pp [Rise|
--   import core
--   fst >> snd >> add 0
-- ]

-- def x : RNat := .nat 4


-- -- #pp [Rise|
-- -- -- instead of def ... : ... := ... (to inline definitions)
-- --   $x
-- -- ]

-- #pp [RiseC|
--   def x : 7·f32
--   take 5 x
-- ]

-- #pp [RiseC|
--   gather
-- ]
-- #pp [RiseC|
--   iterate
-- ]

-- #pp [RiseC|
--   fun(a : 3+5*9·int) => reduce add 0 a
-- ]

-- #pp [RiseC|
--   fun a => reduce add 0 a
-- ]

-- #pp [RiseC|
--   fun a => reduce add 0
-- ]

-- #pp [RiseC|
--   map (fun ab : f32 × f32 => mul (fst ab) (snd ab))
-- ]

-- #pp [RiseC|
--   map (fun ab => mul (fst ab) (snd ab))
-- ]

-- #pp [RiseC|
--   (fun ab => mul (fst ab) (snd ab))
-- ]

-- #pp [RiseC|
--   fun as => fun bs => zip as bs
-- ]

-- #eval toJson [RiseC|
--   (fun (n : nat) => fun (x : n·f32) => x) 2
-- ]

-- #pp [RiseC|
--   (fun (n m : nat) => fun (x : n·m+n·f32) => x) (3+4) 95
-- ]

-- #pp [RiseC|
--   (fun (dt : data) => fun (x : 32·dt) => x) f32
-- ]


-- #pp [RiseC|
--   (fun (dt : data) => ((fun (n : nat) => fun (x : n.dt) => x) (42 : RNat))) (f32 : RData)
-- ]

-- #eval toJson [RiseC| add 0 5]
-- #pp [RiseC| reduce add 0]
-- #pp [RiseC| map transpose]
-- #eval toJson [RiseC| map transpose]

-- #pp [RiseC|
--   def x:4·f32

--   fun n : nat => take n x
-- ]

-- #pp [RiseC|
-- --   // Matrix Matrix muliplication in RISE
-- --   val dot = fun(as, fun(bs,
-- --     zip(as)(bs) |> map(fun(ab, mul(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
-- --   val mm = fun(a : M.K.f32, fun(b : K.N.f32,
-- --     a |> map(fun(arow, // iterating over M
-- --       transpose(b) |> map(fun(bcol, // iterating over N
-- --       dot(arow)(bcol) )))) ) ) // iterating over K
-- --
-- -- Matrix Matrix muliplication in RISE
-- fun a b =>
--   a |> map(fun arow => -- iterating over M
--     transpose(b) |> map(fun bcol => -- iterating over N
--       zip arow bcol |>
--         map (fun ab => mul (fst ab) (snd ab)) |>
--         reduce add 0.0f32)) -- iterating over K
-- ]

-- #pp [RiseC|
--   def x : 7·f32
--   take 5 x
-- ]

-- def x : TypedRExpr := [RiseC| split 128]

-- #pp [RiseC| fun n : nat => $x]

-- TODO: can remove @1 stuff (in types and exprs)
-- ~/tub/masters/shine/src/main/scala/apps/mm,gemmTensor,*,(run tvmgemm)
-- eqsat in nums and/or structural
-- definition inlining


-- from shine/src/test/scala/apps/scal.scala
-- #pp [RiseC|

-- fun n : nat => fun input : n·f32 => fun alpha : f32 =>
--   input |>
--   split (4 * 128 * 128) |>
--   mapPar(
--     asVectorAligned 4 >>
--     split 128 >>
--     mapSeq(mapSeq(fun x =>
--       vectorFromScalar alpha |> mul x
--     )) >> join >> asScalar
--   ) |>
--   join
-- ]

-- #pp [RiseC|
-- fun n : nat => fun input : n·f32 =>
--   input |>
--   split (4 * 128 * 128)
-- ]


-- #pp [RiseC|
--   fun (x : 32·32·f32) =>
--     transpose (transpose x)
-- ]

-- #pp [RiseC| fun (x: 1024·f32) => fun (alpha : f32) =>
--   x |> map (mul alpha)
-- ]

