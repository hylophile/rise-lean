import DPIA.Substitutions
import DPIA.Compilation.Assigning
import DPIA.TypeCheck
import DPIA.mkFunctions

private abbrev mkName := Lean.Name.mkSimple
private abbrev tbc := {node := .lit (.bool false), type := .comm : DPIAPhrase}

mutual
partial def applySubstitution (In phrase : DPIAPhrase) : DPIAPhrase := --- the type is changeing (eliminate the apply in type as well)
    match In.node with
        | .lam name _ body => substitutePhraseInPhrase phrase body name
        | .app fn arg => let sFn := applySubstitution fn arg
                         match sFn.node with
                            | .lam name _ body => substitutePhraseInPhrase phrase body name
                            | _ => panic! s!"the first argument of an apply needs to be a function but is {sFn}"
        | .depapp fn arg => let sFn := applyDepSubstitution fn arg
                            match sFn.node with
                                | .lam name _ body => substitutePhraseInPhrase phrase body name
                                | _ => panic! s!"the first argument of an apply needs to be a function but is {sFn}"

        | _ => panic! s!"{In.node} is not valid function"

partial def applyDepSubstitution (In : DPIAPhrase) (depArg : DWrapper): DPIAPhrase := --- the type is changeing (eliminate the apply in type as well)
    match In.node with
        | .app fn arg => let sFn := applySubstitution fn arg
                         match sFn.node with
                            | .deplam name _ body => substituteDWrapperInPhraseHelper depArg body name 0 --(need a subst function for )
                            | _ => panic! s!"the first argument of an dependent apply needs to be a dependent function but is {sFn}"
        | .depapp fn arg => let sFn := applyDepSubstitution fn arg
                            match sFn.node with
                                | .deplam name _ body => substituteDWrapperInPhraseHelper depArg body name 0 --(need a subst function for )
                                | _ => panic! s!"the first argument of an dependent apply needs to be a dependent function but is {sFn}"
        | .deplam name _ body => substituteDWrapperInPhraseHelper depArg body name 0 --substitutePhraseInPhrase phrase sFn name arg (need a subst function for )
        | _ => panic! s!"{In.node} is not valid dependent function"
end

def accessIsRead (pt : PhraseType) : Bool :=
    match pt with
        | .expr _ .read => true
        | _ => false

def getDataType (pt : PhraseType) : RData :=
    match pt with
        | .expr dt _ => dt
        | _ => panic! s!"something went wrong, this should be an expr type"

def getAccess (pt : PhraseType) : DAnnotation :=
    match pt with
        | .expr _ rw => rw
        | _ => panic! s!"something went wrong, this should be an expr type"

def applyCon (Con phrase : DPIAPhrase) : DPIAPhrase :=
    match Con.node with
        | .lam name _ body => substitutePhraseInPhrase phrase body name
        | _ => panic! s!"the Continuation should be a lambda but is {Con}"

def atIndex (e index : DPIAPhrase) : DPIAPhrase :=
    match index.type,e.type with
        | (.expr (.index n1) _), (.expr (.array n2 dt) _) => if n1 == n2 then mkIdx n1 dt index e
                                                            else panic! s!"the pattern is ({e}, {index}) but expected (expr [idx(n), _], expr[n.dt, _])"
        | _, _ => panic! s!"the pattern is ({e}, {index}) but expected (expr [idx(n), _], expr[n.dt, _])"

def mkVar (dt : RData) : PhraseType := .phrasePair (.expr dt .read) (.acc dt)

def getFromEnv (env : Std.HashMap (Name × Nat) (Name × Nat)) (idx : Nat) (name : Name) : DPIAPhraseNode :=
    .bvar idx name

def getInputDataType (functionalType : PhraseType) : PhraseType :=
    match functionalType with
        | .fn binderType _ => match binderType with
                                | .acc _ => binderType
                                | _ => panic! s!"the input type is supposed to be an acc[dt] type"
        | _ => panic! s!"this is no function type"

mutual
partial def acc (E A : DPIAPhrase) : DPIAPhrase :=
    match E.node with
        | .app fn arg => let sub := applySubstitution fn arg
                         acc sub A
        | .depapp fn arg => let sub := applyDepSubstitution fn arg
                            acc sub A
        | e =>
            if accessIsRead E.type && notContainingArrayType (getDataType E.type)
                then match e with
                        | .functional (.makePair dt1 dt2 _ fst snd) => mkSeq  (acc fst (mkPairAcc1 dt1 dt2 A))
                                                                                    (acc snd  (mkPairAcc2 dt1 dt2 A))
                        | _ => con E {node := .lam (mkName "a") E.type (assignByType (getDataType E.type) A {node := .bvar 0 (mkName "a"), type := E.type}), type := .fn E.type PhraseType.comm}
                else match E.node with
                        | .lit _ => assignByType (getDataType E.type) A E
                        | .bvar _ _ =>  assignByType (getDataType E.type) A E -- at some point i need unique names
                        | .functional func => functionalAcc func E.type A
                        | .ifThenElse cond thenP elseP => let ifThenElse :=  {node := .ifThenElse (mkBvar 0 (mkName "x") cond.type) (acc thenP A) (acc elseP A), type := .comm : DPIAPhrase}
                                                          let cont := mkLam (.fn cond.type .comm) (mkName "x") cond.type ifThenElse
                                                          con cond cont
                        | _ => panic! s!"{E.node} is not valid in an accepter"

partial def functionalAcc (func : FunctionalPrimitives) (type : PhraseType)(A: DPIAPhrase) : DPIAPhrase :=
    match func with
        | .id val => let x := mkBvar 0 (mkName "x") val.type
                     con val
                         (mkLam (.fn type .comm) (mkName "x") val.type
                                (assignByType (getDataType type) A
                                                                 (mkId (getDataType type) x (getAccess type))))
        | .neg val => let x := mkBvar 0 (mkName "x") val.type
                      con val
                          (mkLam (.fn type .comm) (mkName "x") val.type
                                 (assignByType (getDataType type) A
                                                                  (mkNeg (getDataType type) x)))
        | .add lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                                                  (mkAdd (getDataType type) x y)))))
        | .sub lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                                                  (mkSub (getDataType type) x y)))))
        | .mul lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                                                  (mkMul (getDataType type) x y)))))
        | .div lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                                                  (mkDiv (getDataType type) x y)))))
        | .mod lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                                                  (mkMod (getDataType type) x y)))))
        | .not val => let x := mkBvar 0 (mkName "x") val.type
                      con val (mkLam (.fn type .comm) (mkName "x") val.type
                                     (assignByType (getDataType type) A
                                                                      (mkNot x)))
        | .gt lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                         let y := mkBvar 0 (mkName "y") rhs.type
                         con lhs
                             (mkLam (.fn type .comm) (mkName "x") lhs.type
                                    (con rhs
                                         (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                (assignByType (getDataType type) A
                                                                                 (mkGt x y)))))
        | .lt lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                         let y := mkBvar 0 (mkName "y") rhs.type
                         con lhs
                             (mkLam (.fn type .comm) (mkName "x") lhs.type
                                    (con rhs
                                         (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                (assignByType (getDataType type) A
                                                                                 (mkLt x y)))))
        | .equal lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                            let y := mkBvar 0 (mkName "y") rhs.type
                            con lhs
                                (mkLam  (.fn type .comm) (mkName "x") lhs.type
                                        (con rhs
                                             (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                    (assignByType   (getDataType type) A
                                                                                       (mkEqual x y)))))
        | .asScalar n m dt _ array => acc array (mkAsScalarAcc n m dt A)
        | .asVector n m dt _ array => acc array (mkAsVectorAcc n m dt A)
        | .asVectorAligned n m dt _ array => acc array (mkAsVectorAcc n m dt A)
        | .depTile .. => panic! s!"depTile has no scala implementation so there is no lean implementation as well"
        | .idxVec n st idx vec => let xType := PhraseType.expr (.vector n st) .read
                                  let x := mkBvar 0 (mkName "x") xType
                                  con vec
                                      (mkLam (.fn xType .comm) (mkName "x") xType
                                             (assignByType st A (mkIdxVec n st idx x)))
        | .iterate n m k dt f array => tbc
        | .iterateStream n dt1 dt2 f array => tbc
        | .join n m dt _ array => acc array (mkJoinAcc n m dt A)
        | .rlet _ _ _ value f => let x := mkBvar 0 (mkName "x") value.type
                                 con value
                                     (mkLam (.fn value.type .comm) (mkName "x") value.type
                                            (acc (mkApp f.type f x) A))
        | .makePair dt1 dt2 _ fst snd =>  mkSeq (acc fst (mkPairAcc1 dt1 dt2 A))
                                                (acc snd  (mkPairAcc2 dt1 dt2 A))
        | .map n dt1 dt2 _ f array => tbc
        | .mapFst dt1 dt2 dt3 _ f record => tbc
        | .mapSeq unroll n dt _ f array => tbc --con array (mkLam (.fn array.type .comm) (mkName "x") array.type (mkSeq (mkComment "mapSeq") (mkForLoop unroll n (mkLam (.fn ) (mkName "i") )))) --maybe array.type is not correct and we need (.expr (.array n dt) .read)
        | .mapSnd dt1 dt2 dt3 _ f record => tbc
        | .mapVec n dt1 dt2 f array => tbc
        | .padEmpty n r dt array => acc array (mkTakeAcc n r dt A)
        | .printType _ _ _ input => acc input A
        | .reduceSeq _ _ _ dt _ _ _ =>  let rType := PhraseType.expr dt .write
                                        let r := mkBvar 0 (mkName "r") rType
                                        con (mkFunctional type func)
                                            (mkLam  (.fn rType .comm) (mkName "r") rType
                                                    (acc r A))
        | .scanSeq n dt1 dt2 f init array => tbc
        | .scatter n m dt indicies input => let yType := PhraseType.expr (.array n (.index m)) .read
                                            let y := mkBvar 0 (mkName "y") yType
                                            con indicies
                                                (mkLam  (.fn yType .comm) (mkName "y") (.expr (.array n (.index m)) .read)
                                                        (acc input (mkScatterAcc n m dt y A)))
        | .slide n sz _ dt _ => let xType := PhraseType.expr (.array n (.array sz dt)) .read
                                let x := mkBvar 0 (mkName "x") xType
                                con (mkFunctional type func)
                                    (mkLam  (.fn xType .comm) (mkName "x") xType
                                            (assignByType (.array n (.array sz dt)) A x))
        | .split n m dt _ array => acc array (mkSplitAcc n m dt A)
        | .transpose n m dt _ array => acc array (mkTransposeAcc n m dt A)
        | .unzip n dt1 dt2 _ e => acc e (mkUnzipAcc n dt1 dt2 A)
        | .vectorFromScalar n dt arg => let eType := PhraseType.expr dt .read
                                        let e := mkBvar 0 (mkName "e") eType
                                        con arg
                                            (mkLam  (.fn eType .comm) (mkName "e") eType
                                                    (assignByType (.vector n dt) A
                                                                                 (mkVectorFromScalar n dt e)))
        | .zip n dt1 dt2 _ e1 e2 => acc e1 (mkSeq (mkZipAcc1 n dt1 dt2 A) (acc e2 (mkZipAcc2 n dt1 dt2 A)))
        | _ => panic! s!"there is no implementation for {func}"

partial def con (E C : DPIAPhrase) : DPIAPhrase :=
    match E.node with
        | .bvar _ _ => applyCon C E -- C(x)
        | .lit _ => applyCon E C -- C(val)
--        | .imperative imp => imperativeCon imp E.type C
        | .functional func => functionalCon func E.type C
        | .app fn arg => let sub := applySubstitution fn arg
                         con sub C
        | .depapp fn arg => let sub := applyDepSubstitution fn arg
                            con sub C
        | .ifThenElse cond thenP elseP => let ifThenElse :=  {node := .ifThenElse (mkBvar 0 (mkName "x") cond.type) (con thenP C) (con elseP C), type := .comm : DPIAPhrase}
                                          let cont := mkLam (.fn cond.type .comm) (mkName "x") cond.type ifThenElse
                                          con cond cont
        | .proj1 _ | .proj2 _ => applyCon C E
        | _ => panic! s!"{E.node} is not valid in an continuation"

partial def functionalCon (func : FunctionalPrimitives) (type : PhraseType) (C: DPIAPhrase) : DPIAPhrase :=
    match func with
        | .id val => let x := mkBvar 0 (mkName "x") type
                     con val
                         (mkLam (.fn type .comm) (mkName "x") type
                                (applyCon C (mkId (getDataType type) x (getAccess type))))
        | .neg val => let x := mkBvar 0 (mkName "x") type
                      con val
                          (mkLam (.fn type .comm) (mkName "x") type
                                 (applyCon C (mkNeg (getDataType type) x)))
        | .add lhs rhs => let x := mkBvar 1 (mkName "x") type
                          let y := mkBvar 0 (mkName "y") type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C (mkAdd  (getDataType type) x y) ))))
        | .sub lhs rhs => let x := mkBvar 1 (mkName "x") type
                          let y := mkBvar 0 (mkName "y") type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C (mkSub  (getDataType type) x y)))))
        | .mul lhs rhs => let x := mkBvar 1 (mkName "x") type
                          let y := mkBvar 0 (mkName "y") type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C (mkMul (getDataType type) x y)))))
        | .div lhs rhs => let x := mkBvar 1 (mkName "x") type
                          let y := mkBvar 0 (mkName "y") type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C (mkDiv  (getDataType type) x y)))))
        | .mod lhs rhs => let x := mkBvar 1 (mkName "x") type
                          let y := mkBvar 0 (mkName "y") type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C (mkMod  (getDataType type) x y)))))
        | .not val => let x := mkBvar 0 (mkName "x") type
                      con val
                          (mkLam (.fn type .comm) (mkName "x") type
                                 (applyCon C (mkNot x)))
        | .gt lhs rhs =>  let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (applyCon  C (mkGt x y)))))
        | .lt lhs rhs =>  let x := mkBvar 1 (mkName "x") lhs.type
                          let y := mkBvar 0 (mkName "y") rhs.type
                          con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (applyCon  C (mkLt x y)))))
        | .equal lhs rhs => let x := mkBvar 1 (mkName "x") lhs.type
                            let y := mkBvar 0 (mkName "y") rhs.type
                            con lhs
                                (mkLam (.fn type .comm) (mkName "x") lhs.type
                                       (con rhs
                                            (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                   (applyCon  C (mkEqual x y)))))
        | .asScalar n m dt a array => let x := mkBvar 0 (mkName "x") array.type
                                      con array
                                          (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                 (applyCon C (mkAsScalar n m dt a x)))
        | .asVector n m dt a array => let x := mkBvar 0 (mkName "x") array.type
                                      con array
                                          (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                 (applyCon C (mkAsVector n m dt a x)))
        | .asVectorAligned n m dt a array => let x := mkBvar 0 (mkName "x") array.type
                                             con array
                                                 (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                        (applyCon C (mkAsVectorAligned n m dt a x)))
        | .cast dt1 dt2 e => let x := mkBvar 0 (mkName "x") e.type
                             con e
                                 (mkLam (.fn e.type .comm) (mkName "x") e.type
                                        (applyCon C (mkCast dt1 dt2 x)))
        | .drop n m dt array => let x := mkBvar 0 (mkName "x") array.type
                                con array
                                    (mkLam (.fn array.type .comm) (mkName "x") array.type
                                           (applyCon C (mkDrop n m dt x)))
        | .fst dt1 dt2 pair =>  let x := mkBvar 0 (mkName "x") pair.type
                                con pair
                                    (mkLam  (.fn pair.type .comm) (mkName "x") pair.type
                                            (applyCon C (mkFst dt1 dt2 x)))
        | .gather n m dt indicies input =>  let x := mkBvar 0 (mkName "x") input.type
                                            let y := mkBvar 1 (mkName "y") indicies.type
                                            con indicies
                                               (mkLam (.fn indicies.type .comm) (mkName "y") indicies.type
                                                      (con input
                                                           (mkLam (.fn input.type .comm) (mkName "x") input.type
                                                                  (applyCon C (mkGather n m dt y x)))))
        | .generate n dt f => let iType := PhraseType.expr (.index n) .read
                              let i := mkBvar 1 (mkName "i") iType
                              let contType := PhraseType.fn (.expr dt .read) .comm
                              let cont := mkBvar 1 (mkName "cont") contType
                              let gType := PhraseType.expr dt .read
                              let g := mkBvar 0 (mkName "g") gType
                              applyCon C -- needs testing!
                                       (mkGenerateCont n dt
                                                       (mkLam (.fn iType .comm) (mkName "i") iType
                                                              (mkLam (.fn contType .comm) (mkName "cont") contType
                                                                     (applyCon  (applyCon f i)
                                                                                (mkLam  (.fn gType .comm) (mkName "g") gType
                                                                                        (mkApp .comm cont g))))))
        | .idx n dt index array =>  let eType := PhraseType.expr (.array n dt) .read
                                    let e := mkBvar 1 (mkName "e") eType
                                    let i := mkBvar 0 (mkName "i") index.type
                                    con array
                                        (mkLam  (.fn eType .comm) (mkName "e") eType
                                                (con index
                                                     (mkLam (.fn index.type .comm) (mkName "i") index.type
                                                            (applyCon   C
                                                                        (mkIdx n dt i e)))))
        | .indexAsNat n e => let xType := PhraseType.expr (.index n) .read
                             let x := mkBvar 0 (mkName "x") xType
                             con e (mkLam (.fn xType .comm) (mkName "x") xType
                                          (applyCon C (mkIndexAsNat n x)))
        | .join n m dt a array => let xType := PhraseType.expr (.array n (.array m dt)) .read
                                  let x := mkBvar 0 (mkName "x") xType
                                  con array
                                      (mkLam (.fn xType .comm) (mkName "x") xType
                                             (applyCon C (mkJoin n m dt a x)))
        | .rlet _ _ _ val f =>  let x := mkBvar 0 (mkName "x") val.type
                                con val
                                    (mkLam  (.fn val.type .comm) (mkName "x") val.type
                                                (con (applyCon f x) C))
        | .makePair dt1 dt2 a fst snd => let xType := PhraseType.expr dt1 .read
                                         let x := mkBvar 1 (mkName "x") xType
                                         let yType := PhraseType.expr dt2 .read
                                         let y := mkBvar 0 (mkName "y") yType
                                         con fst
                                             (mkLam (.fn xType  .comm) (mkName "x") xType
                                                    (con snd
                                                         (mkLam (.fn yType .comm) (mkName "y") yType
                                                                (applyCon C (mkMakePair dt1 dt2 a x y)))))
        | .map n dt1 dt2 _ f array  =>  let xType := PhraseType.expr (.array n dt1) .read
                                        let x := mkBvar 0 (mkName "x") xType
                                        let aType := PhraseType.expr dt1 .read
                                        let a := mkBvar 1 (mkName "a") aType
                                        let contType := PhraseType.fn (.expr dt2 .read) .comm
                                        let cont := mkBvar 1 (mkName "cont") contType
                                        let bType := PhraseType.expr dt2 .read
                                        let b := mkBvar 0 (mkName "b") bType
                                        con array
                                            (mkLam  (.fn xType .comm) (mkName "x") xType
                                                    (applyCon C (mkMapRead  n dt1 dt2
                                                                            (mkLam  (.fn aType .comm) (mkName "a") aType
                                                                                    (mkLam  (.fn contType .comm) (mkName "cont") contType
                                                                                            (con (applyCon f a)
                                                                                                 (mkLam (.fn bType .comm) (mkName "b") bType
                                                                                                        (mkApp .comm cont b)))))
                                                                            x)))
        | .mapFst dt1 dt2 dt3 a f record => let x := mkBvar 0 (mkName "x") record.type
                                            con record
                                                (mkLam  (.fn record.type .comm) (mkName "x") record.type
                                                        (applyCon C (mkMapFst dt1 dt2 dt3 a f x)))
        | .mapSeq _ n _ dt _ _ => let tmpType := mkVar dt
                                  let tmp := mkBvar 0 (mkName "tmp") tmpType
                                  mkNew (.array n dt) (mkLam (.fn tmpType .comm) (mkName "tmp") tmpType
                                                             (mkSeq (acc (mkFunctional type func) (mkProj2 (.acc dt) tmp))
                                                                    (applyCon C (mkProj1 (.expr dt .read) tmp))))
        | .mapSnd dt1 dt2 dt3 a f record => let x := mkBvar 0 (mkName "x") record.type
                                            con record
                                                (mkLam  (.fn record.type .comm) (mkName "x") record.type
                                                        (applyCon C (mkMapSnd dt1 dt2 dt3 a f x)))
        | .natAsIndex n e => let x := mkBvar 0 (mkName "x") e.type
                             con e (mkLam (.fn e.type .comm) (mkName "x") e.type
                                          (applyCon C (mkNatAsIndex n x)))
        | .padCst n l r dt padExp array =>  let xType := PhraseType.expr (.array n dt) .read
                                            let x := mkBvar 1 (mkName "x") xType
                                            let pType := PhraseType.expr dt .read
                                            let p := mkBvar 0 (mkName "p") pType
                                            con array (mkLam (.fn xType .comm) (mkName "x") xType
                                                            (con padExp (mkLam  (.fn pType .comm) (mkName "p") pType
                                                                                (applyCon C (mkPadCst n l r dt p x )))))
        | .padClamp n l r dt array => let xType := PhraseType.expr (.array n dt) .read
                                      let x := mkBvar 0 (mkName "x") xType
                                      con array
                                          (mkLam (.fn xType .comm) (mkName "x") xType
                                                 (applyCon C (mkPadClamp n l r dt x)))
        | .printType _ _ _ input=> con input C
        | .reduceSeq unroll n dt1 dt2 f init array => let XType := PhraseType.expr (.array n dt1) .read
                                                      let X := mkBvar 1 (mkName "X") XType
                                                      let accum := mkBvar 0 (mkName "accum") (mkVar dt2)
                                                      let iType := PhraseType.expr (.index n) .read
                                                      let i := mkBvar 0 (mkName "i") iType
                                                      con array
                                                          (mkLam (.fn XType .comm) (mkName "X") XType
                                                                 (mkSeq (mkComment "reduceSeq")
                                                                        (mkNew dt2 (mkLam   (.fn (mkVar dt2) (.comm)) (mkName "accum") (mkVar dt2)
                                                                                            (mkSeq  (acc init (mkProj2 (.acc dt2) accum))
                                                                                                    (mkSeq  (mkForLoop unroll n (mkLam  (.fn iType .comm) (mkName "i") iType
                                                                                                                                        (acc (applyCon  (applyCon f (mkProj1 (.expr dt2 .read) accum))
                                                                                                                                                        (atIndex X i))
                                                                                                                                             (mkProj2 (.acc dt2) accum))))
                                                                                                            (applyCon C (mkProj1 (.expr dt2 .read) accum))))))))
        | .scanSeq n _ dt _ _ _ =>  let tmpType :=  mkVar (.array n dt)
                                    let tmp := mkBvar 0 (mkName "tmp") tmpType
                                    mkNew (.array n dt) (mkLam (.fn tmpType .comm) (mkName "tmp") tmpType
                                                               (mkSeq (acc (mkFunctional type func) (mkProj2 (.acc dt) tmp))
                                                                     (applyCon C (mkProj1 (.expr dt .read) tmp))))
        | .slide n sz sp dt input => let inputSize := RNat.plus (.mult sp n) sz
                                     let xType := PhraseType.expr (.array inputSize dt) .read
                                     let x := mkBvar 0 (mkName "x") xType
                                     con input
                                         (mkLam (.fn xType .comm) (mkName "x") xType
                                                (applyCon C (mkSlide n sz sp dt x)))
        | .snd dt1 dt2 pair => let xType := PhraseType.expr (.pair dt1 dt2) .read
                               let x := mkBvar 0 (mkName "x") xType
                               con pair (mkLam  (.fn xType .comm) (mkName "x") xType
                                                (applyCon C (mkSnd dt1 dt2 x)))
        | .split n m dt a array => let xType := PhraseType.expr (.array (.mult m n) dt) .read
                                   let x := mkBvar 0 (mkName "x") xType
                                   con array
                                       (mkLam (.fn xType .comm) (mkName "x") xType
                                              (applyCon C (mkSplit n m dt a x)))
        | .take n m dt array => let xType := PhraseType.expr (.array (.plus n m) dt) .read
                                let x := mkBvar 0 (mkName "x") xType
                                con array (mkLam (.fn xType .comm) (mkName "x") xType
                                                 (applyCon C (mkTake n m dt x)))
        | .toMem dt input => let tmpType := mkVar dt
                             let tmp := mkBvar 0 (mkName "tmp") tmpType
                             mkNew dt (mkLam (.fn tmpType .comm) (mkName "tmp") tmpType
                                             (mkSeq (acc input (mkProj2 (.acc dt) tmp))
                                                    (applyCon C (mkProj1 (.expr dt .read) tmp))))
        | .transpose n m dt a array =>  let x := mkBvar 0 (mkName "x") array.type
                                        con array (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                         (applyCon C (mkTranspose n m dt a x)))
        | .unzip n dt1 dt2 a e => let xType := PhraseType.expr (.array n (.pair dt1 dt2)) .read
                                  let x := mkBvar 0 (mkName "x") xType
                                  con e (mkLam (.fn xType .comm) (mkName "x") xType
                                               (applyCon C (mkUnzip n dt1 dt2 a x)))
        | .vectorFromScalar n dt arg => let eType := PhraseType.expr dt .read
                                        let e := mkBvar 0 (mkName "e") eType
                                        con arg
                                            (mkLam  (.fn eType .comm) (mkName "e") eType
                                                    (applyCon C (mkVectorFromScalar n dt e)))
        | .zip n dt1 dt2 a e1 e2 => let xType := PhraseType.expr (.array n dt1) .read
                                    let x := mkBvar 1 (mkName "x") xType
                                    let yType := PhraseType.expr (.array n dt2) .read
                                    let y := mkBvar 0 (mkName "y") yType
                                    con e1
                                        (mkLam (.fn xType .comm) (mkName "x") xType
                                               (con e2
                                                    (mkLam  (.fn yType .comm) (mkName "y") yType
                                                            (applyCon C (mkZip n dt1 dt2 a x y)))))
        | _ => panic! "this is no Expression Primitive"

partial def fedAcc (env : Std.HashMap (Name × Nat) (Name ×Nat)) (E C : DPIAPhrase) : DPIAPhrase := --type of env not correct yet
    match E.node with
        | .functional func => functionalFed env func E.type C
        | .bvar idx name => applyCon C {node := getFromEnv env idx name, type := E.type}
        | .app fn arg => let sub := applySubstitution fn arg
                         fedAcc env sub C
        | .depapp fn arg => let sub := applyDepSubstitution fn arg
                            fedAcc env sub C
        | .ifThenElse _ _ _ =>  panic! s!"{E.node} is not valid in an fedAcc"
        | .proj1 _ | .proj2 _ => panic! s!"{E.node} is not valid in an fedAcc"
        | _ => panic! s!"{E.node} is not valid in an fedAcc"

partial def functionalFed (env : Std.HashMap (Name × Nat) (Name × Nat)) (func : FunctionalPrimitives) (type : PhraseType) (C : DPIAPhrase) : DPIAPhrase :=
    match func with
        | .asScalar n m dt _ array => let oType := getInputDataType C.type
                                      let o := mkBvar 0 (mkName "o") oType
                                      let returnType := PhraseType.acc (.array m (.vector n dt))
                                      fedAcc env array (mkLam (.fn oType returnType) (mkName "o") oType
                                                              (mkAsScalarAcc n m dt (applyCon C o)))
        | .join n m dt _ array => let oType := getInputDataType C.type
                                  let o := mkBvar 0 (mkName "o") oType
                                  let returnType := PhraseType.acc (.array n (.array m dt))
                                  fedAcc env array (mkLam (.fn oType returnType) (mkName "o") oType
                                                          (mkJoinAcc n m dt (applyCon C o)))
        | .map n dt1 dt2 a f array => tbc
        | .mapFst dt1 dt2 dt3 _ f record => tbc
        | .mapSnd dt1 dt2 dt3 _ f record => tbc
        | .padEmpty n r dt array => let oType := getInputDataType C.type
                                    let o := mkBvar 0 (mkName "o") oType
                                    let returnType := PhraseType.acc (.array n dt)
                                    fedAcc env array (mkLam (.fn oType returnType) (mkName "o") oType
                                                            (mkTakeAcc n r dt (applyCon C o)))
        | .split n m dt _ array =>  let oType := getInputDataType C.type
                                    let o := mkBvar 0 (mkName "o") oType
                                    let returnType := PhraseType.acc (.array (.mult n m) dt)
                                    fedAcc env array (mkLam (.fn oType returnType) (mkName "o") oType
                                                            (mkSplitAcc n m dt (applyCon C o)))
        | .transpose n m dt _ array =>  let oType := getInputDataType C.type
                                        let o := mkBvar 0 (mkName "o") oType
                                        let returnType := PhraseType.acc (.array n (.array m dt))
                                        fedAcc env array (mkLam (.fn oType returnType) (mkName "o") oType
                                                                (mkTransposeAcc n m dt (applyCon C o)))
        | .unzip n dt1 dt2 _ e => let oType := getInputDataType C.type
                                  let o := mkBvar 0 (mkName "o") oType
                                  let returnType := PhraseType.acc (.array n (.pair dt1 dt2))
                                  fedAcc env e (mkLam (.fn oType returnType) (mkName "o") oType
                                                      (mkUnzipAcc n dt1 dt2 (applyCon C o)))
        | _ =>  panic! "this is no Expression Primitive"

partial def str (E C : DPIAPhrase) : DPIAPhrase :=
    match E.node with
        | .functional func => functionalStr func E.type C
        | .app fn arg => let sub := applySubstitution fn arg
                         str sub C
        | .depapp fn arg => let sub := applyDepSubstitution fn arg
                            str sub C
        | _ => translateArrayToStream E C

partial def functionalStr (func : FunctionalPrimitives) (type : PhraseType) (C : DPIAPhrase) : DPIAPhrase :=
    match func with
        | .circularBuffer n alloc size dt1 dt2 load input => tbc
        | .mapStream n dt1 dt2 f array => tbc
        | .rotateValues n size dt a input => tbc
        | .zip n dt1 dt2 _ e1 e2 => tbc
        | _ =>  panic! "this is no Expression Primitive"

partial def translateArrayToStream (E C : DPIAPhrase) : DPIAPhrase :=
    match E.type with
        | .expr (.array n dt) .read => tbc --let depFun := DPIAPhraseNode.deplam (mkName "i") (.rise .nat) (mkLam (.fn ))
                                        --applyCon C depFun
        | _ => panic! s!"cannot translate a non-array type to Stream"
end
