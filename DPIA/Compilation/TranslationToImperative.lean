import DPIA.Substitutions
import DPIA.Compilation.Assigning
import DPIA.TypeCheck
import DPIA.mkFunctions
import DPIA.betaReduction

private abbrev mkName := Lean.Name.mkSimple
private abbrev tbc := {node := .lit (.bool false), type := .comm : DPIAPhrase}
private abbrev Env := List (DPIAPhrase × DPIAPhrase)


def accessIsRead (pt : PhraseType) : Bool :=
    match pt with
        | .expr _ .read => true
        | .pi _ _ body => accessIsRead body
        | .fn _ body => accessIsRead body
        | _ => false


def getAccess (pt : PhraseType) : DAnnotation :=
    match pt with
        | .expr _ rw => rw
        | _ => panic! s!"something went wrong, this should be an expr type"

def applyCon (Con phrase : DPIAPhrase) : DPIAPhrase :=
    betaReduction Con phrase

def atExpr (e index : DPIAPhrase) : DPIAPhrase :=
    match index.type,e.type with
        | (.expr (.index n1) _), (.expr (.array n2 dt) _) => if n1 == n2 then mkIdx n1 dt index e
                                                            else panic! s!"the pattern is ({e.type}, {index.type}) but expected (expr [idx(n), _], expr[n.dt, _])"
        | _, _ => panic! s!"the pattern is ({e.type}, {index.type}) but expected (expr [idx(n), _], expr[n.dt, _])"

def atAcc (e index : DPIAPhrase) : DPIAPhrase :=
    match index.type,e.type with
        | (.expr (.index n1) _), (.acc (.array n2 dt)) => if n1 == n2 then mkIdxAcc n1 dt index e
                                                            else panic! s!"the pattern is ({e.type}, {index.type}) but expected (expr [idx(n), _], expr[n.dt, _])"
        | _, _ =>   panic! s!"the pattern is ({index.type}, {e.type}) but expected (expr [idx(n), _], acc[n.dt])"

def atVec (e index : DPIAPhrase) : DPIAPhrase :=
    match index.type,e.type with
        | (.expr (.index n1) _), (.expr (.vector n2 st) _) => if n1 == n2 then mkIdxVec n1 st index e
                                                            else panic! s!"the pattern is ({e.type}, {index.type}) but expected (expr [idx(n), _], expr[n.dt, _])"
        | _, _ => panic! s!"the pattern is ({e.type}, {index.type}) but expected (expr [idx(n), _], expr[n.dt, _])"

def mkVar (dt : RData) : PhraseType := .phrasePair (.expr dt .read) (.acc dt)

def getFromEnv (env : Env) (idx : Nat) (name : Name) : DPIAPhrase :=
    match env with
        | [] => panic! s!"the key pair ({name},{idx}) was not found in the env"
        | (key, val) :: ys => match key with
                                | ⟨.bvar _ n, .expr _ _⟩ => if n.toString == name.toString
                                                                then match val with
                                                                        | ⟨.bvar _ n, .acc _⟩ => {node := .bvar idx n, type := val.type}
                                                                        |  _ => panic! s!"the key has to be an Identifier of type acc but is {key}"
                                                                else getFromEnv ys idx name
                                | _ => panic! s!"the key has to be an Identifier of type expr but is {key}"

def getType (env : Env) (elem : Nat := 1) : PhraseType :=
    match env with
        | [] => panic! s!"there should be at least one element in here"
        | (key, val) :: _ => if elem == 1
                                then key.type
                                else val.type

def getInputDataType (functionalType : PhraseType) : PhraseType :=
    match functionalType with
        | .fn binderType _ => match binderType with
                                | .acc _ => binderType
                                | _ => panic! s!"the input type is supposed to be an acc[dt] type"
        | _ => panic! s!"this is no function type"


private def mkLamIdx (type : PhraseType) (name : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase) : DPIAPhrase :=
  let indexedBody := adjustIndex body 1 (Std.HashMap.ofList [((name,0), (name,0)) ]) 1
  {node := .lam name binderType indexedBody, type := type : DPIAPhrase}


--------------------------------------- helper functions end -------------------------------------

mutual
partial def acc (E A : DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match E.node with
        | .app fn arg => let sub := betaReduction fn arg
                         acc sub A counter
        | .depapp fn arg => let sub := dependentBetaReduction fn arg
                            acc sub A counter
        | e =>
            if accessIsRead E.type && notContainingArrayType (getDataType E.type)
                then match e with
                        | .functional (.makePair dt1 dt2 _ fst snd) => mkSeq  (acc fst (mkPairAcc1 dt1 dt2 A) counter)
                                                                              (acc snd  (mkPairAcc2 dt1 dt2 A) counter)
                        | _ => con E (fun a => (assignByType (getDataType E.type) A a)) counter
                else match E.node with
                        | .lit _ => assignByType (getDataType E.type) A E
                        | .bvar _ _ =>  assignByType (getDataType E.type) A E
                        | .functional func => functionalAcc func E.type A counter
                        | .ifThenElse cond thenP elseP => con cond (fun cont => mkIfThenElse .comm cont (acc thenP A counter) (acc elseP A counter)) counter
                        | _ => panic! s!"\n{E.node} is not valid in an acceptor"

partial def functionalAcc (func : FunctionalPrimitives) (type : PhraseType) (A: DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match func with
        | .id val => con val (fun x =>
                            (assignByType (getDataType type) A (mkId (getDataType type) x (getAccess type)))) counter
        | .neg val => con val (fun x =>
                            (assignByType (getDataType type) A (mkNeg (getDataType type) x))) counter
        | .add lhs rhs => con lhs (fun x =>
                                con rhs (fun y =>
                                    (assignByType (getDataType type) A (mkAdd (getDataType type) x y))) counter) counter
        | .sub lhs rhs => con lhs (fun x =>
                                con rhs (fun y =>
                                    (assignByType (getDataType type) A (mkSub (getDataType type) x y))) counter) counter
        | .mul lhs rhs => con lhs (fun x =>
                                con rhs (fun y =>
                                    (assignByType (getDataType type) A (mkMul (getDataType type) x y))) counter) counter
        | .div lhs rhs => con lhs (fun x =>
                                con rhs (fun y =>
                                    (assignByType (getDataType type) A (mkDiv (getDataType type) x y))) counter) counter
        | .mod lhs rhs => con lhs (fun x =>
                            con rhs (fun y =>
                                 (assignByType (getDataType type) A (mkMod (getDataType type) x y))) counter) counter
        | .not val => con val (fun x =>
                               (assignByType (getDataType type) A (mkNot x))) counter
        | .gt lhs rhs => con lhs (fun x =>
                             con rhs (fun y =>
                                 (assignByType (getDataType type) A (mkGt x y))) counter) counter
        | .lt lhs rhs => con lhs (fun x =>
                            con rhs (fun y =>
                                (assignByType (getDataType type) A (mkLt x y))) counter) counter
        | .equal lhs rhs => con lhs (fun x =>
                                con rhs (fun y =>
                                    (assignByType   (getDataType type) A (mkEqual x y))) counter) counter
        | .asScalar n m dt _ array => acc array (mkAsScalarAcc n m dt A) counter
        | .asVector n m dt _ array => acc array (mkAsVectorAcc n m dt A) counter
        | .asVectorAligned n m dt _ array => acc array (mkAsVectorAcc n m dt A) counter
        | .depTile .. => panic! s!"depTile has no scala implementation so there is no lean implementation as well"
        | .idxVec n st idx vec => con vec (fun x =>
                                      (assignByType st A (mkIdxVec n st idx x))) counter
        | .iterate n m k dt f array => tbc -- con array (fun x =>
                                                         -- let sz := RNat.mult (.pow n k) m
                                                         -- mkNewDoubleBuffer sz (.array sz dt) (.array m dt) (.array sz dt) x A (mkLamIdx
                                                                                                                                  --                                                                         (mkLamIdx
                                                                                                                                                                                                              --                                                                             (mkLamIdx))))
        | .iterateStream .. => tbc -- not necessary for my bachelor thesis
        | .join n m dt _ array => acc array (mkJoinAcc n m dt A) counter
        | .rlet _ _ _ value f => con value (fun x =>
                                     (acc (mkApp f.type f x) A counter))  counter
        | .makePair dt1 dt2 _ fst snd =>  mkSeq (acc fst (mkPairAcc1 dt1 dt2 A) counter)
                                                (acc snd  (mkPairAcc2 dt1 dt2 A) counter)
        | .map n dt1 dt2 _ f array => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt1 .write)
                                      let oType := PhraseType.acc dt2
                                      let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType
                                      let i := mkBvar 0 (mkName "i") oType
                                      acc array
                                          (mkMapAcc n dt2 dt1
                                                    (mkLamIdx  (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                            (fedAcc ((x, o) :: []) (applyCon f x)
                                                                        (mkLamIdx (.fn oType oType) (mkName "i") oType i)
                                                                        (counter +1)))
                                                    A) (counter +1)
        | .mapFst dt1 dt2 dt3 _ f record => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt1 .write)
                                            let oType := PhraseType.acc dt3
                                            let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType
                                            let i := mkBvar 0 (mkName "i") oType
                                            acc record
                                                (mkMapFstAcc dt1 dt2 dt3
                                                            (mkLamIdx  (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                                    (fedAcc ((x, o) :: []) (applyCon f x)
                                                                            (mkLamIdx (.fn oType oType) (mkName "i") oType i)
                                                                            (counter +1)))
                                                            A) (counter +1)
        | .mapSeq unroll n _ _ f array =>  let iType := PhraseType.expr (.index n) .read
                                           let i := mkBvar 0 (mkName "i") iType
                                           con  array (fun x =>
                                                 (mkSeq  (mkComment "mapSeq")
                                                               (mkForLoop unroll n (mkLamIdx (.fn iType .comm) (mkName "i") iType
                                                                                             (acc (applyCon f (atExpr x i))
                                                                                                  (atAcc A i) counter))))) counter
        | .mapSnd dt1 dt2 dt3 _ f record => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt2 .write)
                                            let oType := PhraseType.acc dt3
                                            let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType
                                            let i := mkBvar 0 (mkName "i") oType
                                            acc record
                                                (mkMapFstAcc dt1 dt2 dt3
                                                            (mkLamIdx  (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                                    (fedAcc ((x, o) :: []) (applyCon f x)
                                                                            (mkLamIdx (.fn oType oType) (mkName "i") oType i)
                                                                            (counter +1)))
                                                            A) (counter +1)
        | .mapVec n _ dt2 f array =>    let iType := PhraseType.expr (.index n) .read
                                        let i := mkBvar 1 (mkName "i") iType
                                        let aType := PhraseType.acc dt2
                                        let a:= mkBvar 0 (mkName "a") aType
                                        con array (fun x =>
                                            (mkForVec n dt2 A (mkLamIdx (.fn iType .comm) (mkName "i") iType
                                                                        (mkLamIdx (.fn aType .comm) (mkName "a") aType
                                                                                  (acc  (applyCon f (atVec x i))
                                                                                        a counter))))) counter
        | .padEmpty n r dt array => acc array (mkTakeAcc n r dt A) counter
        | .printType _ _ _ input => acc input A counter
        | .reduceSeq _ _ _ _ _ _ _ =>  con (mkFunctional type func) (fun r =>
                                                (acc r A counter)) counter
        | .scanSeq n _ dt2 f init array =>  let accumType := mkVar dt2
                                            let accum0 := mkBvar 0 (mkName "accum") accumType
                                            let iType := PhraseType.expr (.index n) .read
                                            let i := mkBvar 0 (mkName "i") iType
                                            con array
                                                (fun x=>
                                                        (con init
                                                             (fun y =>
                                                                    (mkSeq  (mkComment "scanSeq")
                                                                            (mkNew  dt2
                                                                                    (mkLamIdx  (.fn accumType .comm) (mkName "accum") accumType
                                                                                            (mkSeq  (acc y (mkProj2 (.acc dt2) accum0) counter)
                                                                                                    (mkForLoop  false n
                                                                                                                (mkSeq  (acc (applyCon  (applyCon f (atExpr x i))
                                                                                                                                        (mkProj1 (.expr dt2 .read) accum0))
                                                                                                                             (mkProj2 (.acc dt2) accum0) counter)
                                                                                                                        (assignByType dt2 (atAcc A i) (mkProj1 (.expr dt2 .read) accum0)))))))))
                                                             counter))
                                                counter
        | .scatter n m dt indicies input => con indicies (fun y =>
                                               (acc input (mkScatterAcc n m dt y A) counter)) counter
        | .slide n sz _ dt _ => con (mkFunctional type func) (fun x =>
                                    (assignByType (.array n (.array sz dt)) A x)) counter
        | .split n m dt _ array => acc array (mkSplitAcc n m dt A) counter
        | .transpose n m dt _ array => acc array (mkTransposeAcc n m dt A) counter
        | .unzip n dt1 dt2 _ e => acc e (mkUnzipAcc n dt1 dt2 A) counter
        | .vectorFromScalar n dt arg => con arg
                                            (fun e =>
                                                    (assignByType (.vector n dt) A
                                                                                 (mkVectorFromScalar n dt e))) counter
        | .zip n dt1 dt2 _ e1 e2 => acc e1 (mkSeq (mkZipAcc1 n dt1 dt2 A) (acc e2 (mkZipAcc2 n dt1 dt2 A) counter)) counter
        | _ => panic! s!"there is no implementation for {func}"

partial def con (E : DPIAPhrase) (C : DPIAPhrase → DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match E.node with
        | .bvar _ _ =>C E -- C(x)
        | .lit _ => C E -- C(val)
--        | .imperative imp => imperativeCon imp E.type C
        | .functional func => functionalCon func E.type C counter
        | .app fn arg => let sub := betaReduction fn arg
                         con sub C counter
        | .depapp fn arg => let sub := dependentBetaReduction fn arg
                            con sub C counter
        | .ifThenElse cond thenP elseP => let ifThenElse :=  fun cont => {node := .ifThenElse cont (con thenP C counter) (con elseP C counter), type := .comm : DPIAPhrase}
                                          con cond ifThenElse counter
        | .proj1 _ | .proj2 _ => C E
        | _ => panic! s!"{E.node} is not valid in an continuation"


partial def functionalCon (func : FunctionalPrimitives) (type : PhraseType) (C: DPIAPhrase → DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match func with
        | .id val => con val (fun x =>
                          (C (mkId (getDataType type) x (getAccess type)))) counter
        | .neg val => con val (fun x =>
                          (C (mkNeg (getDataType type) x))) counter
        | .add lhs rhs => con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkAdd  (getDataType type) x y) )) counter)) counter
        | .sub lhs rhs => con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkSub  (getDataType type) x y))) counter)) counter
        | .mul lhs rhs => con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkMul (getDataType type) x y))) counter)) counter
        | .div lhs rhs => con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkDiv  (getDataType type) x y))) counter)) counter
        | .mod lhs rhs => con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkMod  (getDataType type) x y))) counter)) counter
        | .not val => con val (fun x =>
                          (C (mkNot x))) counter
        | .gt lhs rhs =>  con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkGt x y))) counter)) counter
        | .lt lhs rhs =>  con lhs (fun x =>
                              (con rhs (fun y =>
                                   (C (mkLt x y))) counter)) counter
        | .equal lhs rhs => con lhs (fun x =>
                                (con rhs (fun y =>
                                     (C (mkEqual x y))) counter)) counter
        | .asScalar n m dt a array => con array (fun x =>
                                          (C (mkAsScalar n m dt a x))) counter
        | .asVector n m dt a array => con array (fun x =>
                                          (C (mkAsVector n m dt a x))) counter
        | .asVectorAligned n m dt a array => con array (fun x =>
                                                 (C (mkAsVectorAligned n m dt a x))) counter
        | .cast dt1 dt2 e => con e (fun x =>
                                 (C (mkCast dt1 dt2 x))) counter
        | .drop n m dt array => con array (fun x =>
                                    (C (mkDrop n m dt x))) counter
        | .fst dt1 dt2 pair =>  con pair (fun x =>
                                    (C (mkFst dt1 dt2 x))) counter
        | .gather n m dt indicies input =>  con indicies (fun y =>
                                                (con input (fun x =>
                                                     (C (mkGather n m dt y x))) counter)) counter
        | .generate n dt f => let iType := PhraseType.expr (.index n) .read
                              let i := mkBvar 0 (mkName "i") iType
                              let contType := PhraseType.fn (.expr dt .read) .comm
                              let cont := mkBvar 0 (mkName "cont") contType
                              let gType := PhraseType.expr dt .read
                              let g := mkBvar 0 (mkName "g") gType
                              C -- needs testing!
                                       (mkGenerateCont n dt
                                                       (mkLamIdx (.fn iType .comm) (mkName "i") iType
                                                              (mkLamIdx (.fn contType .comm) (mkName "cont") contType
                                                                     (applyCon  (applyCon f i)
                                                                                (mkLamIdx  (.fn gType .comm) (mkName "g") gType
                                                                                        (mkApp .comm cont g))))))
        | .idx n dt index array =>  con array (fun e =>
                                        (con index (fun i =>
                                            (C (mkIdx n dt i e))) counter)) counter
        | .indexAsNat n e => con e (fun x =>
                                (C (mkIndexAsNat n x))) counter
        | .join n m dt a array => con array (fun x =>
                                        (C (mkJoin n m dt a x))) counter
        | .rlet _ _ _ val f =>  con val (fun x =>
                                     (con (applyCon f x) C counter)) counter
        | .makePair dt1 dt2 a fst snd => con fst (fun x =>
                                            (con snd (fun y =>
                                                (C (mkMakePair dt1 dt2 a x y))) counter)) counter
        | .map n dt1 dt2 _ f array  =>  let aType := PhraseType.expr dt1 .read
                                        let a := mkBvar 1 (mkName "a") aType
                                        let contType := PhraseType.fn (.expr dt2 .read) .comm
                                        let cont := mkBvar 0 (mkName "cont") contType
                                        con array
                                            (fun x =>
                                                    (C (mkMapRead  n dt1 dt2
                                                                            (mkLamIdx  (.fn aType .comm) (mkName "a") aType
                                                                                    (mkLamIdx  (.fn contType .comm) (mkName "cont") contType
                                                                                            (con (applyCon f a)
                                                                                                 (fun b =>
                                                                                                        (mkApp .comm cont b)) counter)))
                                                                            x))) counter
        | .mapFst dt1 dt2 dt3 a f record => con record (fun x =>
                                                (C (mkMapFst dt1 dt2 dt3 a f x))) counter
        | .mapSeq _ n _ dt _ _ => let tmpType := mkVar dt
                                  let tmp := mkBvar 0 (mkName "tmp") tmpType
                                  mkNew (.array n dt) (mkLamIdx (.fn tmpType .comm) (mkName "tmp") tmpType
                                                             (mkSeq (acc (mkFunctional type func) (mkProj2 (.acc dt) tmp) counter)
                                                                    (C (mkProj1 (.expr dt .read) tmp))))
        | .mapSnd dt1 dt2 dt3 a f record => con record (fun x =>
                                                (C (mkMapSnd dt1 dt2 dt3 a f x))) counter
        | .natAsIndex n e => con e (fun x =>
                                (C (mkNatAsIndex n x))) counter
        | .padCst n l r dt padExp array =>  con array (fun x =>
                                                (con padExp (fun p =>
                                                    (C (mkPadCst n l r dt p x ))) counter)) counter
        | .padClamp n l r dt array => con array (fun x =>
                                        (C (mkPadClamp n l r dt x))) counter
        | .printType _ _ _ input=> con input C counter
        | .reduceSeq unroll n _ dt2 f init array => let accum0 := mkBvar 0 (mkName "accum") (mkVar dt2)
                                                    let iType := PhraseType.expr (.index n) .read
                                                    let i := mkBvar 0 (mkName "i") iType
                                                    con array (fun X =>
                                                        (mkSeq  (mkComment "reduceSeq")
                                                                (mkNew dt2 (mkLamIdx (.fn (mkVar dt2) (.comm)) (mkName "accum") (mkVar dt2)
                                                                                     (mkSeq  (mkSeq  (acc init (mkProj2 (.acc dt2) accum0) counter)
                                                                                                     (mkForLoop unroll n (mkLamIdx  (.fn iType .comm) (mkName "i") iType
                                                                                                                                    (acc (applyCon  (applyCon f (mkProj1 (.expr dt2 .read) accum0))
                                                                                                                                                    (atExpr X i))
                                                                                                                                         (mkProj2 (.acc dt2) accum0) counter))))
                                                                                             (C (mkProj1 (.expr dt2 .read) accum0))))))) counter
        | .scanSeq n _ dt _ _ _ =>  let tmpType :=  mkVar (.array n dt)
                                    let tmp := mkBvar 0 (mkName "tmp") tmpType
                                    mkNew (.array n dt) (mkLamIdx (.fn tmpType .comm) (mkName "tmp") tmpType
                                                                  (mkSeq (acc (mkFunctional type func) (mkProj2 (.acc dt) tmp) counter)
                                                                         (C (mkProj1 (.expr dt .read) tmp))))
        | .slide n sz sp dt input => con input (fun x =>
                                         (C (mkSlide n sz sp dt x))) counter
        | .snd dt1 dt2 pair => con  pair (fun x =>
                                    (C (mkSnd dt1 dt2 x))) counter
        | .split n m dt a array => con array (fun x =>
                                       (C (mkSplit n m dt a x))) counter
        | .take n m dt array => con array (fun x =>
                                    (C (mkTake n m dt x))) counter
        | .toMem dt input => let tmpType := mkVar dt
                             let tmp := mkBvar 0 (mkName "tmp") tmpType
                             mkNew dt (mkLamIdx (.fn tmpType .comm) (mkName "tmp") tmpType
                                             (mkSeq (acc input (mkProj2 (.acc dt) tmp) counter)
                                                    (C (mkProj1 (.expr dt .read) tmp))))
        | .transpose n m dt a array =>  con array (fun x =>
                                            (C (mkTranspose n m dt a x))) counter
        | .unzip n dt1 dt2 a e => con e (fun x =>
                                    (C (mkUnzip n dt1 dt2 a x))) counter
        | .vectorFromScalar n dt arg => con arg (fun e =>
                                            (C (mkVectorFromScalar n dt e))) counter
        | .zip n dt1 dt2 a e1 e2 => con e1 (fun x =>
                                    (con e2 (fun y =>
                                         (C (mkZip n dt1 dt2 a x y))) counter )) counter
        | _ => panic! "this is no Expression Primitive"

partial def fedAcc (env : Env) (E C : DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match E.node with
        | .functional func => functionalFed env func C counter
        | .bvar idx name => applyCon C (getFromEnv env idx name)
        | .app fn arg => let sub := betaReduction fn arg
                         fedAcc env sub C counter
        | .depapp fn arg => let sub := dependentBetaReduction fn arg
                            fedAcc env sub C counter
        | .ifThenElse _ _ _ =>  panic! s!"{E.node} is not valid in an fedAcc"
        | .proj1 _ | .proj2 _ => panic! s!"{E.node} is not valid in an fedAcc"
        | _ => panic! s!"{E.node} is not valid in an fedAcc"

partial def functionalFed (env : Env) (func : FunctionalPrimitives) (C : DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match func with
        | .asScalar n m dt _ array => let oType := getInputDataType C.type
                                      let o := mkBvar 0 (mkName "o") oType
                                      let returnType := PhraseType.acc (.array m (.vector n dt))
                                      fedAcc env array (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                              (mkAsScalarAcc n m dt (applyCon C o))) counter
        | .join n m dt _ array => let oType := getInputDataType C.type
                                  let o := mkBvar 0 (mkName "o") oType
                                  let returnType := PhraseType.acc (.array n (.array m dt))
                                  fedAcc env array (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                          (mkJoinAcc n m dt (applyCon C o))) counter
        | .map n dt1 dt2 a f array => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt1 a)
                                      let oType := PhraseType.acc dt2
                                      let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType -- there is a probelm with the debruijn identifier for o that needs to be solved
                                      let y := mkBvar 0 (mkName "y") (getType env)
                                      fedAcc env array
                                             (mkLamIdx (.fn (getType env) (.acc (.array n dt1))) (mkName "y") (getType env)
                                                    (mkMapAcc n
                                                              dt2
                                                              dt1
                                                              (mkLamIdx (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                                     (fedAcc ((x,o) :: env)
                                                                             (applyCon f x)
                                                                             (mkLamIdx (.fn oType oType) (mkName "i") oType
                                                                                    (mkBvar 0 (mkName "i") oType)) (counter +1)))
                                                              (applyCon C y)))
                                             (counter +1)
        | .mapFst dt1 dt2 dt3 _ f record => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt2 .write)
                                            let oType := PhraseType.acc dt3
                                            let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType -- there is a probelm with the debruijn identifier for o that needs to be solved
                                            let y := mkBvar 0 (mkName "y") (getType env 2)
                                            fedAcc env record
                                                    (mkLamIdx (.fn (getType env 2) (.acc (.pair dt1 dt2))) (mkName "y") (getType env 2)
                                                            (mkMapFstAcc dt1 dt2 dt3
                                                                        (mkLamIdx (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                                                (fedAcc ((x,o) :: env)
                                                                                        (applyCon f x)
                                                                                        (mkLamIdx (.fn oType oType) (mkName "i") oType
                                                                                                (mkBvar 0 (mkName "i") oType)) (counter +1)))
                                                                        (applyCon C y)))
                                                    (counter +1)
        | .mapSnd dt1 dt2 dt3 _ f record => let x := mkBvar 0 (getFreshIdentifier "fede_x" counter) (.expr dt2 .write)
                                            let oType := PhraseType.acc dt3
                                            let o := mkBvar 0 (getFreshIdentifier "fede_o" counter) oType -- there is a probelm with the debruijn identifier for o that needs to be solved
                                            let y := mkBvar 0 (mkName "y") (getType env 2)
                                            fedAcc env record
                                                    (mkLamIdx (.fn (getType env 2) (.acc (.pair dt1 dt2))) (mkName "y") (getType env 2)
                                                            (mkMapSndAcc dt1 dt2 dt3
                                                                        (mkLamIdx (.fn oType oType) (getFreshIdentifier "fede_o" counter) oType
                                                                                (fedAcc ((x,o) :: env)
                                                                                        (applyCon f x)
                                                                                        (mkLamIdx (.fn oType oType) (mkName "i") oType
                                                                                                (mkBvar 0 (mkName "i") oType)) (counter +1)))
                                                                        (applyCon C y)))
                                                    (counter +1)
        | .padEmpty n r dt array => let oType := getInputDataType C.type
                                    let o := mkBvar 0 (mkName "o") oType
                                    let returnType := PhraseType.acc (.array n dt)
                                    fedAcc env array (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                            (mkTakeAcc n r dt (applyCon C o))) counter
        | .split n m dt _ array =>  let oType := getInputDataType C.type
                                    let o := mkBvar 0 (mkName "o") oType
                                    let returnType := PhraseType.acc (.array (.mult n m) dt)
                                    fedAcc env array (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                            (mkSplitAcc n m dt (applyCon C o))) counter
        | .transpose n m dt _ array =>  let oType := getInputDataType C.type
                                        let o := mkBvar 0 (mkName "o") oType
                                        let returnType := PhraseType.acc (.array n (.array m dt))
                                        fedAcc env array (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                                (mkTransposeAcc n m dt (applyCon C o))) counter
        | .unzip n dt1 dt2 _ e => let oType := getInputDataType C.type
                                  let o := mkBvar 0 (mkName "o") oType
                                  let returnType := PhraseType.acc (.array n (.pair dt1 dt2))
                                  fedAcc env e (mkLamIdx (.fn oType returnType) (mkName "o") oType
                                                      (mkUnzipAcc n dt1 dt2 (applyCon C o))) counter
        | _ =>  panic! "this is no Expression Primitive"

-- not necessary for my bachelor thesis
partial def str (E C : DPIAPhrase) (counter : Nat): DPIAPhrase :=
    match E.node with
        | .functional func => functionalStr func E.type C counter
        | .app fn arg => let sub := betaReduction fn arg
                         str sub C counter
        | .depapp fn arg => let sub := dependentBetaReduction fn arg
                            str sub C counter
        | _ => translateArrayToStream E C

-- not necessary for my bachelor thesis
partial def functionalStr (func : FunctionalPrimitives) (_ : PhraseType) (_ : DPIAPhrase) (_ : Nat): DPIAPhrase :=
    match func with
        | .circularBuffer .. => tbc
        | .mapStream .. => tbc
        | .rotateValues .. => tbc
        | .zip .. => tbc
        | _ =>  panic! "this is no Expression Primitive"

-- not necessary for my bachelor thesis
partial def translateArrayToStream (E _ : DPIAPhrase) : DPIAPhrase :=
    match E.type with
        | .expr (.array ..) .read => tbc
        | _ => panic! s!"cannot translate a non-array type to Stream"
end

partial def translationToImperative (p : DPIAPhrase) : DPIAPhrase :=
    let outT := p.type
    let out := mkBvar 0 (mkName "output") (.acc (getDataType outT))
    acc p out 0
