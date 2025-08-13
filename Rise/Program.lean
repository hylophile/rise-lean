import Rise.Type
import Rise.TypedRExpr
import Lean
open Lean Elab Meta


-- structure RResult where
--   expr : TypedRExpr
--   type : RType


-- instance : ToString RResult where
--   toString x := s!"\nexpr:\n{x.expr}\ntype:\n{x.type}"

-- instance [ToExpr α] : ToExpr (Except String α) where
--   toExpr
--   | .error s => mkApp3 (Expr.const ``Except.error [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr s)
--   | .ok a => mkApp3 (Expr.const ``Except.ok [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr a)
--   toTypeExpr := mkApp2 (Expr.const ``Except [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α)

-- instance : ToExpr RResult where
--   toExpr r :=
--     let exprExpr := toExpr r.expr
--     let typeExpr := toExpr r.type
--     mkAppN (mkConst ``RResult.mk) #[exprExpr, typeExpr]
--   toTypeExpr := mkConst ``RResult

declare_syntax_cat  rise_decl
syntax "def" ident ":" rise_type  : rise_decl
syntax rise_decl rise_decl        : rise_decl
syntax "import" "core"            : rise_decl

-- TODO : a rise program could have more than one expr
declare_syntax_cat  rise_program
syntax (rise_decl)? rise_expr : rise_program

partial def elabRDeclAndRExpr (e: Syntax) : Option Syntax → RElabM Expr
  | some d_stx =>
    match d_stx with
    | `(rise_decl| def $x:ident : $t:rise_type $decl:rise_decl ) => do
      let t ← elabToRType t
      -- Lean.logInfo m!"found {x.getId} : {t}"
      withNewGlobalTerm (x.getId, t) do elabRDeclAndRExpr e (some decl)

    | `(rise_decl| def $x:ident : $t:rise_type ) => do
      let t ← elabToRType t
      -- Lean.logInfo m!"found {x.getId} : {t}"
      withNewGlobalTerm (x.getId, t) do elabRDeclAndRExpr e none

    | _ => throwUnsupportedSyntax
  | none => do
      let e ← elabToTypedRExpr e
      let e ← applyUnifyResultsRecursivelyUntilStable e
      -- let t ← inferAux e
      -- let t ← applyUnifyResults t
      -- dbg_trace (← ur)
      return toExpr e

partial def elabRProgram : Syntax → RElabM Expr
  | `(rise_program| $d:rise_decl $e:rise_expr ) => do
    elabRDeclAndRExpr e (some d)
  | `(rise_program| $e:rise_expr ) => do
    elabRDeclAndRExpr e none
  | _ => throwUnsupportedSyntax

elab "[Rise|" p:rise_program "]" : term => do
  let p ← liftMacroM <| expandMacros p
  liftToTermElabM <| elabRProgram p

set_option hygiene false in
macro_rules
  | `(rise_decl| import core) => `(rise_decl|
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
  -- def select : {t : data} → bool → t → t → t

  -- -- comparison ops
  -- def not   :               bool → bool
  -- def gt    : {t : data} → t → t → bool
  -- def lt    : {t : data} → t → t → bool
  -- def equal : {t : data} → t → t → bool

  -- cast ops
  def cast : {s t : data} → s → t
  -- TODO: what's natType? the type nat (as opposed to the kind nat)?
  -- def indexAsNat : {n : nat} → idx[n] → natType
  -- def natAsIndex : (n : nat) → natType → idx[n]

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
  -- TODO: vector types (need additional parameter)
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
  -- added because it was found in a scalar file
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
  def iterate : {n m k : nat} → {t : data} → ((l : nat) → (l*n)·t → l·t) → (m*(n^k))·t → m·t



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

    
  )

elab "[RiseC|" p:rise_expr "]" : term => do
  let p ← `(rise_program| import core $p:rise_expr)
  let p ← liftMacroM <| expandMacros p
  liftToTermElabM <| elabRProgram p

-------------------------------------------------------------------------

syntax "#pp " term : command
macro_rules
| `(#pp $e) => `(#eval IO.print <| toString $e)


-- #check [Rise|
-- def map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n·δ1 → n·δ2
-- def reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n·δ → δ
-- def add : {δ : data} → δ → δ → δ
-- def mul : {δ : data} → δ → δ → δ
-- def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
-- def snd : {δ1 δ2 : data} → δ1 × δ2 → δ1
-- def zip : {n : nat} → {δ1 δ2 : data} → n·δ1 → n·δ2 → n·(δ1 × δ2)

-- fun as => fun bs =>
--      zip as bs |> map (fun ab => mul (fst ab) (snd ab)) |> reduce add 0
-- ]

-- #check [Rise|
--   import core

--   fun as => fun bs =>
--        zip as bs |> map (fun ab => mul (fst ab) (snd ab)) |> reduce add 0
-- ]

#pp [RiseC|
  fun as => fun bs =>
      -- todo: we shouldn't need these parens i guess
       zip as bs |> map (fun ab => mul (fst ab) (snd ab)) |> reduce add 0
]

-- #pp [RiseC|
--   fun(k : nat) => fun(a : k·scalar) => reduce add 0 a
-- ]

#pp [RiseC|
  fun x:2·3·scalar => concat (x |> transpose |> join) (x |> join) 
]

#pp [RiseC|
  take 5
]
#eval [RiseC|
  take
]

#pp [RiseC|
  circularBuffer
]

#pp [RiseC|
  fst >> snd >> add 0
]




#pp [RiseC|
  test 5
]
#eval [RiseC|
  test 5
]

#pp [RiseC|
  gather
]
#pp [RiseC|
  iterate
]

#pp [RiseC|
  fun(a : 3+5*9·scalar) => reduce add 0 a
]

#pp [RiseC|
  fun a => reduce add 0 a
]

#pp [RiseC|
  fun a => reduce add 0
]

-- #pp [RiseC|
--   map (fun ab : scalar × scalar => mul (fst ab) (snd ab))
-- ]
#pp [RiseC|
  map (fun ab => mul (fst ab) (snd ab))
]

#pp [RiseC|
  (fun ab => mul (fst ab) (snd ab))
]

#pp [RiseC|
  fun as => fun bs => zip as bs
]

#pp [RiseC| add 0 5]
#pp [RiseC| reduce add 0]
#pp [RiseC| map transpose]
#eval toJson [RiseC| map transpose]


#eval toJson [RiseC|
--   // Matrix Matrix muliplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mul(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.scalar, fun(b : K.N.scalar,
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
        reduce add 0)) -- iterating over K
]

#eval [RiseC|
  fun (n : nat) => fun input : n·scalar => (split 8) input
]

-- from shine/src/test/scala/apps/scal.scala
#eval [RiseC|
fun(n: nat) => fun(input : n·scalar) => fun(alpha : scalar) =>
  input |>
  -- inlining this for now
  -- split (mul 4 (mul 128 128)) |>
  split 65536 |>
  mapPar(
    asVectorAligned(4) >>
    split(128) >>
    mapSeq(mapSeq(fun x =>
      vectorFromScalar(alpha) |> mul x
    )) >> join >> asScalar
  ) |>
  join

]



#pp [RiseC|
  fun (x : 32·32·scalar) =>
    transpose (transpose x)
]

#eval [RiseC| fun (x: 1024·scalar) => fun (alpha : scalar) =>
  x |> map (mul alpha)
]
