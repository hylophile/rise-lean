import Rise.Type
import Rise.TypedRExpr
import Lean

open Lean Elab Meta

set_option pp.raw true
set_option pp.raw.maxDepth 10

declare_syntax_cat                 rise_decl
syntax "def" ident ":" rise_type                        : rise_decl
-- without separating with ;, the rise_expr is overlapping with the
-- first and only rise_expr of rise_program. there is probably a way to
-- make rise_expr's whitespace-sensitive, but this will do for now
-- syntax "def" ident (":" rise_type)? ":=" rise_expr ";"  : rise_decl
syntax "import" "core"                                  : rise_decl

-- TODO : a rise program could have more than one expr
declare_syntax_cat              rise_program
syntax (rise_decl)* rise_expr : rise_program

unsafe def elabRDeclAndRExpr (expr: Syntax) (decls : List (TSyntax `rise_decl)) : RElabM Expr :=
  match decls with
  | [] => do
      let expr ← elabToTypedRExpr expr
      let expr ← applyUnifyResultsRecursivelyUntilStable expr
      return toExpr expr

  | decl :: rest =>
    match decl with
    | `(rise_decl| def $x:ident : $t:rise_type) => do
      let t ← elabToRType t
      -- let _ ← Term.addTermInfo x (toExpr t.toString) -- meh
      withNewGlobalTerm (x.getId, t) do elabRDeclAndRExpr expr rest

    -- | `(rise_decl| def $x:ident := $e:rise_expr;) => do
    --   let e ← elabToTypedRExpr e
    --   -- let e := {e with type := (← addImplicits e.type)}
    --   withNewGlobalTerm (x.getId, e.type) do elabRDeclAndRExpr expr rest

    -- | `(rise_decl| def $x:ident : $t_syn:rise_type := $e:rise_expr;) => do
    --   let t ← elabToRType t_syn
    --   let e ← elabToTypedRExpr e
    --   let e := {e with type := (← addImplicits e.type)}
    --   if t.unify e.type == .none then throwErrorAt x s!"cannot unify type annotation '{t_syn.raw.prettyPrint}' with inferred type '{e.type}'"
    --   withNewGlobalTerm (x.getId, t) do elabRDeclAndRExpr expr rest

    | s => throwErrorAt s m!"{s}"
    -- | _ => throwUnsupportedSyntax

unsafe def elabRProgram : Syntax → RElabM Expr
  | `(rise_program| $d:rise_decl* $e:rise_expr) => do
    elabRDeclAndRExpr e d.toList
  | s => throwErrorAt s m!"{s}"
    -- | _ => throwUnsupportedSyntax

elab "[Rise|" p:rise_program "]" : term => unsafe do
  let p ← liftMacroM <| expandMacros p
  liftToTermElabM <| elabRProgram p

set_option hygiene false in
macro_rules
  | `(rise_program| import core
      $[$d]* $e:rise_expr) => `(rise_program|
  -- unary ops
  def id  : {t : data} → t → t
  def neg : {t : data} → t → t
  -- binary ops
  def add : {t : data} → t → t → t
  def sub : {t : data} → t → t → t
  def mul : {t : data} → t → t → t
  def div : {t : data} → t → t → t
  def mod : {t : data} → t → t → t

  -- -- ternary ops
  def select : {t : data} → bool → t → t → t

  -- -- comparison ops
  def not   :               bool → bool
  def gt    : {t : data} → t → t → bool
  def lt    : {t : data} → t → t → bool
  def equal : {t : data} → t → t → bool

  -- cast ops
  def cast : {s t : data} → s → t
  -- TODO: what's natType? the type nat (as opposed to the kind nat)?
  def indexAsNat : {n : nat} → idx[n] → natType
  def natAsIndex : (n : nat) → natType → idx[n]

  -- memory ops
  -- (can't use "let" as identifier)
  def  rlet : {s t : data} → s → (s → t) → t
  def toMem : {t : data} → t → t

  -- foreign functions
  -- def foreignFunctionCall(funDecl : rise.core.ForeignFunction.Decl, n : Int):
  --     n*((inTs : data) →) (outT : data) → n*(*inTs →) outT
  -- can ignore for now
  -- n args, with different

  -- array ops
  -- def makeArray(n : Int): {dt : data} → n*(dt →) n·dt

  def generate : {n : nat} → {t : data} → (idx[n] → t) → n·t
  def      idx : {n : nat} → {t : data} → idx[n] → n·t → t

  def   take : (n : nat) → {  m : nat} → {t : data} → (n+m)·t → n·t
  def   drop : (n : nat) → {  m : nat} → {t : data} → (n+m)·t → m·t
  def concat :             {n m : nat} → {t : data} → n·t → m·t → (n+m)·t

  def split : (n : nat) → {  m : nat} → {t : data} → (m*n)·t → m·n·t
  def  join :             {n m : nat} → {t : data} → n·m·t → (n*m)·t

  def          slide : {n : nat} → (sz sp    : nat) → {  t : data} → (sp*n+sz)·t → (1+n)·sz·t
  def circularBuffer : {n : nat} → (alloc sz : nat) → {s t : data} → (s → t) → (n-1+sz)·s → n·sz·t
  def   rotateValues : {n : nat} → (sz       : nat) → {  t : data} → (t → t) → (n-1+sz)·t → n·sz·t

  def transpose : {n m : nat} → {t : data} → n·m·t → m·n·t

  def  gather : {n m : nat} → {t : data} → m·idx[n] → n·t → m·t
  def scatter : {n m : nat} → {t : data} → n·idx[m] → n·t → m·t
  -- TODO: type-level functions
  -- def reorder : {t : data} → (n : nat) → (idxF : nat2nat) → (idxFinv : nat2nat) → n·t → n·t

  def padCst :   {n : nat} → (l r : nat) → {t : data} → t → n·t → (l+n+r)·t
  def padClamp : {n : nat} → (l r : nat) → {t : data} →     n·t → (l+n+r)·t
  def padEmpty : {n : nat} → (  r : nat) → {t : data} →     n·t →   (n+r)·t

  def   zip : {n : nat} → {s t : data} → n·s → n·t → n·(s × t)
  def unzip : {n : nat} → {s t : data} → n·(s × t) → (n·s × n·t)

  -- pair ops
  def makePair : {s t : data} → s → t → (s × t)
  def      fst : {s t : data} → (s × t) → s
  def      snd : {s t : data} → (s × t) → t

  -- vector ops
  def vectorFromScalar : {n : nat} → {t : data} → t → n<t>
  def asVector :         (n : nat) → {m : nat} → {t : data} → (m*n)·t → m·n<t>
  def asVectorAligned :  (n : nat) → {m : nat} → {t : data} → (m*n)·t → m·n<t>
  def asScalar :         {n : nat} → {m : nat} → {t : data} → m·n<t> → (m*n)·t

  -- map
  def map           : {n : nat} → {s t : data} → (s → t) → n·s → n·t
  def mapSeq        : {n : nat} → {s t : data} → (s → t) → n·s → n·t
  def mapSeqUnroll  : {n : nat} → {s t : data} → (s → t) → n·s → n·t
  def mapStream     : {n : nat} → {s t : data} → (s → t) → n·s → n·t
  def iterateStream : {n : nat} → {s t : data} → (s → t) → n·s → n·t
  -- added because it was found in a scala file
  def mapPar        : {n : nat} → {s t : data} → (s → t) → n·s → n·t

  def mapFst : {s1 t  s2 : data} → (s1 → s2) → (s1 × t) → (s2 × t)
  def mapSnd : {s  t1 t2 : data} → (t1 → t2) → (s × t1) → (s × t2)

  -- reduce
  def reduce :          {n : nat} → {  t : data} → (t → t → t) → t → n·t → t
  def reduceSeq :       {n : nat} → {s t : data} → (t → s → t) → t → n·s → t
  def reduceSeqUnroll : {n : nat} → {s t : data} → (t → s → t) → t → n·s → t

  -- scan
  def scanSeq : {n : nat} → {s : data} → {t : data} → (s → t → t) → t → n·s → n·t

  -- vvv interesting
  -- iterate
  def iterate : {n m k : nat} →
  {t : data} → ((l : nat) → (l*n)·t → l·t) → (m*(n^k))·t → m·t



  -- vvv ignore
  -- dependent pair ops
  -- def makeDepPair : {fdt : nat2data} → (n : nat) → fdt(n) → (m : nat ** fdt(m))
  -- def dmatch :      {fdt : nat2data} → {t : data} → (n : nat ** fdt(n)) → ((m : nat) → fdt(m) → t) → t

  -- dependent array ops
  -- def depMapSeq : {n : nat} → {ft1 : nat2data} → {ft2 : nat2data} →
  --     ((k : nat) → ft1(k) → ft2(k)) → n..ft1 → n..ft2
  -- def depZip : {n : nat} → {ft1 : nat2data} → {ft2 : nat2data} →
  --     n..ft1 → n..ft2 → n..(i : nat |→ (ft1(i), ft2(i)) )
  -- def depJoin : {n : nat} → {lenF : nat2nat} → {t : data} →
  --     n..(i : nat |→ lenF(i)·t) → (sum_(i=0)^(n-1) lenF(i))·t
  -- def partition : {n : nat} → {t : data} → (m : nat) → (lenF : nat2nat) → n·t → m..(i : nat |→ lenF(i)·t)


  $[$d]*

  $e:rise_expr
)

elab "[RiseC|" ds:rise_decl* e:rise_expr "]" : term => unsafe do
  let p ← `(rise_program| import core
            $[$ds:rise_decl]* $e:rise_expr)
  let p ← liftMacroM <| expandMacros p
  liftToTermElabM <| elabRProgram p

-------------------------------------------------------------------------

syntax "#pp " term : command
macro_rules
| `(#pp $e) => `(#eval IO.print <| toString $e)

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

#eval toJson [RiseC| add 0 5]
-- #pp [RiseC| reduce add 0]
-- #pp [RiseC| map transpose]
-- #eval toJson [RiseC| map transpose]
#pp [RiseC|
(fun I : f32 → f32 => I) id

]

#pp [RiseC|
--   // Matrix Matrix muliplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mul(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.f32, fun(b : K.N.f32,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K
--
-- Matrix Matrix muliplication in RISE
fun a b =>
  a |> map(fun arow => -- iterating over M
    transpose(b) |> map(fun bcol => -- iterating over N
      zip arow bcol |>
        map (fun ab => mul (fst ab) (snd ab)) |>
        reduce add 0.0f32)) -- iterating over K
]

/--
error: cannot unify application of 'take 5' to 'x':
(5+?m₀)·?t₁ != 7·f32
---
error: cannot unify application of 'take 5' to 'x':
(5+?m₀)·?t₁ != 7·f32
---
error: rdata: unknown identifier x
---
error: rnat: unknown identifier x
---
error: unification failed
---
error: Only found errors under all interpretations
-/
#guard_msgs in
#pp [RiseC|
  def x : 7·f32
  take 5 x
]

-- from shine/src/test/scala/apps/scal.scala
#pp [RiseC|
fun n : nat => fun input : n·f32 => fun alpha : f32 =>
  input |>
  split (4 * 128 * 128) |>
  mapPar(
    asVectorAligned 4 >>
    split 128 >>
    mapSeq(mapSeq(fun x =>
      vectorFromScalar alpha |> mul x
    )) >> join >> asScalar
  ) |>
  join
]

#eval [RiseC|
fun n : nat => fun input : n·f32 => fun alpha : f32 =>
  input |>
  split (4 * 128 * 128)
]


#pp [RiseC|
  fun (x : 32·32·f32) =>
    transpose (transpose x)
]

#pp [RiseC| fun (x: 1024·f32) => fun (alpha : f32) =>
  x |> map (mul alpha)
]
