import DPIA.InferAccessAnnotation
import Rise
import DPIA.FromRise
import DPIA.Printing

def prodMult := [RiseC| fun d : data => fun xs : d × d => xs.1 * xs.2]
#pp prodMult

#eval inferAccess prodMult

def foo := [RiseC| fun y : f32 => (fun x : f32 =>  x * y) y ]
#pp foo

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq ($prodMult f32)|> toMem |> reduceSeq add 0.0f32
]

def simpleZip := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> mapSeq ($prodMult f32)
]

def applyInferAccessToDot := inferAccess dot

#pp dot
#pp fromRise dot

#pp simpleZip
#pp fromRise simpleZip
#pp inferAccess simpleZip
#pp fromRise dot


-- Λ(n7 : nat) =>
-- 	λ(e8 : exp[n7.f32, read]) =>
-- 		λ(e9 : exp[n7.f32, read]) =>
-- 			((λ(x120 : (exp[(f32, f32), read]) -> exp[f32, write]) =>
-- 				λ(x121 : exp[n7.(f32, f32), read]) =>
-- 					MapSeq(false) λ(e1 : exp[(f32, f32), read]) =>
-- 									((λ(x122 : exp[f32, read]) =>
-- 										λ(x123 : exp[f32, read]) =>
-- 											BinOp(*,(x122 : exp[f32, read]),(x123 : exp[f32, read]))
-- 											(λ(x124 : exp[(f32, f32), read]) =>
-- 												Fst(f32,f32,(x124 : exp[(f32, f32), read])) (e1 : exp[(f32, f32), read])))
-- 									(λ(x125 : exp[(f32, f32), read]) =>
-- 										Snd(f32,f32,(x125 : exp[(f32, f32), read]))
-- 										(e1 : exp[(f32, f32), read]))))
-- 			((λ(x126 : exp[n7.f32, read]) =>
-- 				λ(x127 : exp[n7.f32, read]) =>
-- 					Zip(n7,f32,f32,read,(x126 : exp[n7.f32, read]),(x127 : exp[n7.f32, read]))
-- 				(e8 : exp[n7.f32, read]))
-- 			(e9 : exp[n7.f32, read])))
















--  Λ(n : nat) =>
-- 	λ(as : exp[n.f32, read]) =>
--     λ(bs : exp[n.f32, read]) =>
--         (((λ(x81 : (exp[f32, read]) -> (exp[f32, read]) -> exp[f32, write]) =>
--             λ(x82 : exp[f32, write]) =>
-- 				λ(x83 : exp[n.f32, read]) =>
-- 					ReduceSeq(false) λ(e2 : exp[f32, read]). λ(e3 : exp[f32, read]).
-- 					((λ(x84 : exp[f32, read]).
-- 					λ(x85 : exp[f32, read]). BinOp(+,(x84 : exp[f32, read]),(x85 : exp[f32, read])) (e2 : exp[f32, read])) (e3 : exp[f32, read]))) Literal(0.0f))
-- 					(λ(x86 : exp[n.f32, write]). ToMem(n.f32,(x86 : exp[n.f32, write])) ((λ(x87 : (exp[(f32, f32), read]) -> exp[f32, write]). λ(x88 : exp[n.(f32, f32), read]).
-- 					MapSeq(false) λ(e1 : exp[(f32, f32), read]). ((λ(x89 : exp[f32, read]). λ(x90 : exp[f32, read]). BinOp(*,(x89 : exp[f32, read]),(x90 : exp[f32, read])) (λ(x91 : exp[(f32, f32), read]).
-- 					Fst(f32,f32,(x91 : exp[(f32, f32), read])) (e1 : exp[(f32, f32), read]))) (λ(x92 : exp[(f32, f32), read]). Snd(f32,f32,(x92 : exp[(f32, f32), read])) (e1 : exp[(f32, f32), read])))) ((λ(x93 : exp[n.f32, read]). λ(x94 : exp[n.f32, read]).
-- 					Zip(n,f32,f32,read,(x93 : exp[n.f32, read]),(x94 : exp[n.f32, read])) (as : exp[n.f32, read])) (bs : exp[n.f32, read])))))




-- { mapSeq <λe1. mul (fst e1) (snd e1)> (zip e8 e9)=exp[n7.f32, write],
-- λe9. mapSeq <λe1. mul (fst e1) (snd e1)> (zip e8 e9)=(exp[n7.f32, read]) -> exp[n7.f32, write],
-- e9=exp[n7.f32, read],  zip e8 e9=exp[n7.(f32, f32), read],
-- mul=(exp[f32, read]) -> (exp[f32, read]) -> exp[f32, read],
-- e9=exp[n7.f32, read],
-- mul (fst e1)=(exp[f32, read]) -> exp[f32, read],
-- λe1. mul (fst e1) (snd e1)=(exp[(f32, f32), read]) -> exp[f32, read],
-- fst=(exp[(f32, f32), read]) -> exp[f32, read],
-- zip=(exp[n7.f32, read]) -> (exp[n7.f32, read]) -> exp[n7.(f32, f32), read],
-- λe8. λe9. mapSeq <λe1. mul (fst e1) (snd e1)> (zip e8 e9)=(exp[n7.f32, read]) -> (exp[n7.f32, read]) -> exp[n7.f32, write],
-- mul (fst e1) (snd e1)=exp[f32, read],
-- e1=exp[(f32, f32), read],
-- zip e8=(exp[n7.f32, read]) -> exp[n7.(f32, f32), read],
-- snd e1=exp[f32, read],
-- e1=exp[(f32, f32), read],
-- mapSeq=((exp[(f32, f32), read]) -> exp[f32, write]) -> (exp[n7.(f32, f32), read]) -> exp[n7.f32, write],
-- snd=(exp[(f32, f32), read]) -> exp[f32, read],
-- e8=exp[n7.f32, read],  e8=exp[n7.f32, read],
-- fst e1=exp[f32, read],
-- mapSeq <λe1. mul (fst e1) (snd e1)>=(exp[n7.(f32, f32), read]) -> exp[n7.f32, write],
-- e1=exp[(f32, f32), read],
-- Λn7:nat. λe8. λe9. mapSeq <λe1. mul (fst e1) (snd e1)> (zip e8 e9)=(n7: nat) -> (exp[n7.f32, read]) -> (exp[n7.f32, read]) -> exp[n7.f32, write]}
