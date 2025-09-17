import Rise.Main

#eval runEgg "hi"

def main : IO Unit := do
  IO.println ""
-- example program
--   // Matrix Matrix Multiplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.float, fun(b : K.N.float,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K

-- RISE
--
-- Syntax of Expressions and Types:
--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
--   δ ::= n.δ | δ × δ | idx [n] | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--
-- High-Level Primitives:
--                 id : (δ : data) → δ → δ
--   add | mult | ... : (δ : data) → δ → δ → δ
--                fst : (δ1 δ2 : data) → δ1 × δ2 → δ1
--                snd : (δ1 δ2 : data) → δ1 × δ2 → δ2
--                map : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
--             reduce : (n : nat) → (δ : data) → (δ → δ → δ) → δ → n.δ → δ
--                zip : (n : nat) → (δ1 δ2 : data) → n.δ1 → n.δ2 → n.(δ1 × δ2)
--              split : (n m : nat) → (δ : data) → nm.δ → n.m.δ
--               join : (n m : nat) → (δ : data) → n.m.δ → nm.δ
--          transpose : (n m : nat) → (δ : data) → n.m.δ → m.n.δ
--           generate : (n : nat) → (δ : data) → (idx [n] → δ) → n.δ
--
-- Low-Level Primitives:
--   map{Seq|SeqUnroll|Par} : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
--    reduce{Seq|SeqUnroll} : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--                    toMem : (δ1 δ2 : data) → δ1 → (δ1 → δ2) → δ2
--                   mapVec : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n<δ1> → n<δ2>
--                 asVector : (n m : nat) → (δ : data) → nm.δ → n.m<δ>
--                 asScalar : (n m : nat) → (δ : scalar) → n.m<δ, actually scalar> → nm.δ

--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--vector 2,4,8,16
-- e.g. 16vfloat, 16_float
-- idx, range 0 to n excluding

-- https://github.com/rise-lang/shine/blob/main/src/main/scala/rise/core/types/ExprType.scala
-- https://github.com/rise-lang/shine/blob/main/src/main/scala/rise/core/Expr.scala
-- example code benchmarks

