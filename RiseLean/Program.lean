import RiseLean.Type
import RiseLean.Expr
import RiseLean.Check
import Lean
open Lean Elab Meta


structure RResult where
  expr : RExpr
  type : RType


instance : ToString RResult where
  toString x := s!"\nexpr:\n{x.expr}\ntype:\n{x.type}"

-- instance [ToExpr α] : ToExpr (Except String α) where
--   toExpr
--   | .error s => mkApp3 (Expr.const ``Except.error [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr s)
--   | .ok a => mkApp3 (Expr.const ``Except.ok [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr a)
--   toTypeExpr := mkApp2 (Expr.const ``Except [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α)

instance : ToExpr RResult where
  toExpr r :=
    let exprExpr := toExpr r.expr
    let typeExpr := toExpr r.type
    mkAppN (mkConst ``RResult.mk) #[exprExpr, typeExpr]
  toTypeExpr := mkConst ``RResult

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
      let e ← elabToRExpr e
      let t ← inferAux e
      -- let t ← applyUnifyResults t
      dbg_trace (← ur)
      return toExpr <| RResult.mk e t

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
    def map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n·δ1 → n·δ2
    def reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n·δ → δ
    def add : {δ : data} → δ → δ → δ
    def mult : {δ : data} → δ → δ → δ
    def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
    def snd : {δ1 δ2 : data} → δ1 × δ2 → δ2
    def zip : {n : nat} → {δ1 δ2 : data} → n·δ1 → n·δ2 → n·(δ1 × δ2)
    def transpose : {n m : nat} → {δ : data} → n·m·δ → m·n·δ

    def mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2
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
-- def mult : {δ : data} → δ → δ → δ
-- def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
-- def snd : {δ1 δ2 : data} → δ1 × δ2 → δ1
-- def zip : {n : nat} → {δ1 δ2 : data} → n·δ1 → n·δ2 → n·(δ1 × δ2)

-- fun as => fun bs =>
--      zip as bs |> map (fun ab => mult (fst ab) (snd ab)) |> reduce add 0
-- ]

-- #check [Rise|
--   import core

--   fun as => fun bs =>
--        zip as bs |> map (fun ab => mult (fst ab) (snd ab)) |> reduce add 0
-- ]

#pp [RiseC|
  fun as => fun bs =>
      -- todo: we shouldn't need these parens i guess
       (zip as bs |> map (fun ab => mult (fst ab) (snd ab))) |> reduce add 0
]

-- #pp [RiseC|
--   fun(k : nat) => fun(a : k·scalar) => reduce add 0 a
-- ]

#pp [RiseC|
  fun(a : 3·scalar) => reduce add 0 a
]

#pp [RiseC|
  fun a => reduce add 0 a
]

#pp [RiseC|
  fun a => reduce add 0
]

-- #pp [RiseC|
--   map (fun ab : scalar × scalar => mult (fst ab) (snd ab))
-- ]
#pp [RiseC|
  map (fun ab => mult (fst ab) (snd ab))
]

-- todo: should we know from this that ab : ?d1 x ?d2 ? yes.
-- i think if we find that a subst already exists in unifyresults,
-- we should unify those too. if you know what i mean.
#pp [RiseC|
  (fun ab => mult (fst ab) (snd ab))
]

#pp [RiseC|
  fun as => fun bs => zip as bs
]

#pp [RiseC| add 0 5]
#pp [RiseC| reduce add 0]
#pp [RiseC| map transpose]


#pp [RiseC|
--   // Matrix Matrix Multiplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.scalar, fun(b : K.N.scalar,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K
-- 
-- Matrix Matrix Multiplication in RISE
fun a b =>
  a |> map(fun arow => -- iterating over M
    transpose(b) |> map(fun bcol => -- iterating over N
      zip arow bcol |>
        map (fun ab => mult (fst ab) (snd ab)) |>
        reduce add 0)) -- iterating over K
]

#pp [RiseC|
  fun (x : 32 . 32 .float) =>
    transpose (transpose x)
]
#eval [RiseC| fun (x: 1024 . float) => fun (alpha : float) =>
  x |> map (mult alpha)
]
