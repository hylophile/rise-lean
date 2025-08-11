import RiseLean.Program

-- RISE
--
-- Syntax of Expressions and Types:
--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
--   δ ::= n.δ | δ × δ | idx [n] | scalar | n<scalar>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--

-- example program
--   // Matrix Matrix Multiplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.scalar, fun(b : K.N.scalar,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K


-- High-Level Primitives:
--         id : {δ : data} → δ → δ
--        add : {δ : data} → δ → δ → δ
--       mult : {δ : data} → δ → δ → δ
--       todo : {δ : data} → δ → δ → δ
--        fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
--        snd : {δ1 δ2 : data} → δ1 × δ2 → δ2
--        map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
--        zip : {n : nat} → {δ1 δ2 : data} → n.δ1 → n.δ2 → n.(δ1 × δ2)
--      split : (n : nat) → {m : nat} → {δ : data} → nm.δ → n.m.δ
--       join : {n m : nat} → {δ : data} → n.m.δ → nm.δ
--  transpose : {n m : nat} → {δ : data} → n.m.δ → m.n.δ
--   generate : {n : nat} → {δ : data} → (idx [n] → δ) → n.δ

-- Low-Level Primitives:
--           mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     mapSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--           mapPar : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--        reduceSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--  reduceSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--            toMem : {δ1 δ2 : data} → δ1 → {δ1 → δ2} → δ2 -- TODO: very different type in shine repo
--           mapVec : {n : nat} → {δ1 δ2 : data} → {δ1 → δ2} → n<δ1> → n<δ2> -- TODO: doesn't exist in shine repo
--         asVector : (n : nat) → {m : nat} → {δ : data} → nm.δ → m.n<δ>
--         asScalar : {n m : nat} → {δ : data} → n.m<δ> → nm.δ


