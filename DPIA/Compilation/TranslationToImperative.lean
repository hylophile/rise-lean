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
        | .id val => con val (mkLam (.fn type .comm) (mkName "x") val.type (assignByType (getDataType type) A (mkId (getDataType type) (mkBvar 0 (mkName "x") val.type) (getAccess type))))
        | .neg val => con val (mkLam (.fn type .comm) (mkName "x") val.type (assignByType (getDataType type) A (mkNeg (getDataType type) (mkBvar 0 (mkName "x") val.type))))
        | .add lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkAdd (getDataType type) (mkBvar 1 (mkName "x") lhs.type)
                                                                                         (mkBvar 0 (mkName "y") rhs.type))))))
        | .sub lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkSub (getDataType type) (mkBvar 1 (mkName "x") lhs.type)
                                                                                         (mkBvar 0 (mkName "y") rhs.type))))))
        | .mul lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkMul (getDataType type) (mkBvar 1 (mkName "x") lhs.type)
                                                                                         (mkBvar 0 (mkName "y") rhs.type))))))
        | .div lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkDiv (getDataType type) (mkBvar 1 (mkName "x") lhs.type)
                                                                                         (mkBvar 0 (mkName "y") rhs.type))))))
        | .mod lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkMod (getDataType type) (mkBvar 1 (mkName "x") lhs.type)
                                                                                         (mkBvar 0 (mkName "y") rhs.type))))))
        | .not val => con val (mkLam (.fn type .comm) (mkName "x") val.type (assignByType (getDataType type) A (mkNot (mkBvar 0 (mkName "x") val.type))))
        | .gt lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkGt (mkBvar 1 (mkName "x") lhs.type)
                                                                     (mkBvar 0 (mkName "y") rhs.type))))))
        | .lt lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (assignByType (getDataType type) A
                                                               (mkLt (mkBvar 1 (mkName "x") lhs.type)
                                                                     (mkBvar 0 (mkName "y") rhs.type))))))
        | .equal lhs rhs => con lhs
                                (mkLam  (.fn type .comm) (mkName "x") lhs.type
                                        (con rhs
                                             (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                    (assignByType   (getDataType type) A
                                                                    (mkEqual (mkBvar 1 (mkName "x") lhs.type)
                                                                             (mkBvar 0 (mkName "y") rhs.type))))))
        | .asScalar n m dt _ array => acc array (mkAsScalarAcc n m dt A)
        | .asVector n m dt _ array => acc array (mkAsVectorAcc n m dt A)
        | .asVectorAligned n m dt _ array => acc array (mkAsVectorAcc n m dt A)
        | .depTile .. => panic! s!"depTile has no scala implementation so there is no lean implementation as well"
        | .idxVec n st idx vec => con vec (mkLam (.fn vec.type .comm) (mkName "x") vec.type (assignByType st A (mkIdxVec n st idx (mkBvar 0 (mkName "x") vec.type)))) -- maybe vector.type is not correct and it needs to be .expr (.vector n st) .read
        | .iterate n m k dt f array => tbc
        | .iterateStream n dt1 dt2 f array => tbc
        | .join n m dt _ array => acc array (mkJoinAcc n m dt A)
        | .rlet _ _ _ value f => con value (mkLam (.fn value.type .comm) (mkName "x") value.type (acc (mkApp f.type f (mkBvar 0 (mkName "x") value.type)) A))
        | .makePair dt1 dt2 _ fst snd =>  mkSeq (acc fst (mkPairAcc1 dt1 dt2 A))
                                                (acc snd  (mkPairAcc2 dt1 dt2 A))
        | .map n dt1 dt2 _ f array => tbc
        | .mapFst dt1 dt2 dt3 _ f record => tbc
        | .mapSeq unroll n dt _ f array => tbc --con array (mkLam (.fn array.type .comm) (mkName "x") array.type (mkSeq (mkComment "mapSeq") (mkForLoop unroll n (mkLam (.fn ) (mkName "i") )))) --maybe array.type is not correct and we need (.expr (.array n dt) .read)
        | .mapSnd dt1 dt2 dt3 _ f record => tbc
        | .mapVec n dt1 dt2 f array => tbc
        | .padEmpty n r dt array => acc array (mkTakeAcc n r dt A)
        | .printType _ _ _ input => acc input A
        | .reduceSeq _ _ _ dt _ _ _ => con {node:= .functional func, type := type} (mkLam (.fn (.expr dt .write) .comm) (mkName "r") (.expr dt .write) (acc (mkBvar 0 (mkName "r") (.expr dt .write)) A))
        | .scanSeq n dt1 dt2 f init array => tbc
        | .scatter n m dt indicies input => con indicies (mkLam (.fn (.expr (.array n (.index m)) .read) .comm) (mkName "y") (.expr (.array n (.index m)) .read) (acc input (mkScatterAcc n m dt (mkBvar 0 (mkName "y") (.expr (.array n (.index m)) .read)) A)))
        | .slide n sz _ dt _ => con {node := .functional func, type := type} (mkLam (.fn (.expr (.array n (.array sz dt)) .read) .comm) (mkName "x") (.expr (.array n (.array sz dt)) .read) (assignByType (.array n (.array sz dt)) A (mkBvar 0 (mkName "x") (.expr (.array n (.array sz dt)) .read))))
        | .split n m dt _ array => acc array (mkSplitAcc n m dt A)
        | .transpose n m dt _ array => acc array (mkTransposeAcc n m dt A)
        | .unzip n dt1 dt2 _ e => acc e (mkUnzipAcc n dt1 dt2 A)
        | .vectorFromScalar n dt arg => con arg (mkLam (.fn arg.type .comm) (mkName "e") arg.type (assignByType (.vector n dt) A (mkVectorFromScalar n dt (mkBvar 0 (mkName "e") arg.type)))) -- not sure if arg.type correct or maybe (.expr dt .read)
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
        | .id val => con val (mkLam (.fn type .comm) (mkName "x") type (applyCon C (mkId (getDataType type) (mkBvar 0 (mkName "x") type) (getAccess type))))
        | .neg val => con val (mkLam (.fn type .comm) (mkName "x") type (applyCon C (mkNeg (getDataType type) (mkBvar 0 (mkName "x") type))))
        | .add lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C
                                                            (mkAdd  (getDataType type) (mkBvar 1 (mkName "x") type)
                                                                    (mkBvar 0 (mkName "y") type))))))
        | .sub lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C
                                                            (mkSub  (getDataType type) (mkBvar 1 (mkName "x") type)
                                                                    (mkBvar 0 (mkName "y") type))))))
        | .mul lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C
                                                            (mkMul  (getDataType type) (mkBvar 1 (mkName "x") type)
                                                                    (mkBvar 0 (mkName "y") type))))))
        | .div lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C
                                                            (mkDiv  (getDataType type) (mkBvar 1 (mkName "x") type)
                                                                    (mkBvar 0 (mkName "y") type))))))
        | .mod lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") type
                                                 (applyCon C
                                                            (mkMod  (getDataType type) (mkBvar 1 (mkName "x") type)
                                                                    (mkBvar 0 (mkName "y") type))))))
        | .not val => con val (mkLam (.fn type .comm) (mkName "x") type (applyCon C (mkNot (mkBvar 0 (mkName "x") type))))
        | .gt lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (applyCon  C
                                                            (mkGt (mkBvar 1 (mkName "x") lhs.type)
                                                                  (mkBvar 0 (mkName "y") rhs.type))))))
        | .lt lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (applyCon  C
                                                            (mkLt (mkBvar 1 (mkName "x") lhs.type)
                                                                  (mkBvar 0 (mkName "y") rhs.type))))))
        | .equal lhs rhs => con lhs
                              (mkLam (.fn type .comm) (mkName "x") lhs.type
                                     (con rhs
                                          (mkLam (.fn type .comm) (mkName "y") rhs.type
                                                 (applyCon  C
                                                            (mkEqual (mkBvar 1 (mkName "x") lhs.type)
                                                                     (mkBvar 0 (mkName "y") rhs.type))))))
        | .asScalar n m dt a array => con array
                                          (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                 (applyCon C (mkAsScalar n m dt a (mkBvar 0 (mkName "x") array.type))))
        | .asVector n m dt a array => con array
                                          (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                 (applyCon C (mkAsVector n m dt a (mkBvar 0 (mkName "x") array.type))))
        | .asVectorAligned n m dt a array => con array
                                                 (mkLam (.fn array.type .comm) (mkName "x") array.type
                                                        (applyCon C (mkAsVectorAligned n m dt a (mkBvar 0 (mkName "x") array.type))))
        | .cast dt1 dt2 e => con e
                                 (mkLam (.fn e.type .comm) (mkName "x") e.type
                                        (applyCon C (mkCast dt1 dt2 (mkBvar 0 (mkName "x") e.type))))
        | .drop n m dt array => con array
                                    (mkLam (.fn array.type .comm) (mkName "x") array.type
                                           (applyCon C (mkDrop n m dt (mkBvar 0 (mkName "x") array.type))))
        | .fst dt1 dt2 pair => con pair
                                   (mkLam (.fn pair.type .comm) (mkName "x") pair.type
                                          (applyCon C (mkFst dt1 dt2 (mkBvar 0 (mkName "x") pair.type))))
        | .gather n m dt indicies input => con indicies
                                               (mkLam (.fn indicies.type .comm) (mkName "y") indicies.type
                                                      (con input
                                                           (mkLam (.fn input.type .comm) (mkName "x") input.type
                                                                  (applyCon C (mkGather n m dt
                                                                                        (mkBvar 1 (mkName "y") indicies.type)
                                                                                        (mkBvar 0 (mkName "x") input.type))))))
        | .generate n dt f => applyCon C -- needs testing!
                                       (mkGenerateCont n dt
                                                       (mkLam (.fn (.expr (.index n) .read) .comm) (mkName "i") (.expr (.index n) .read)
                                                              (mkLam (.fn (.fn (.expr dt .read) .comm) .comm) (mkName "cont") (.fn (.expr dt .read) .comm)
                                                                     (applyCon  (applyCon f (mkBvar 1 (mkName "i") (.expr (.index n) .read)))
                                                                                (mkLam  (.fn (.expr dt .read) .comm) (mkName "g") (.expr dt .read)
                                                                                        (mkApp .comm
                                                                                               (mkBvar 1 (mkName "cont") (.fn (.expr dt .read) .comm))
                                                                                               (mkBvar 0 (mkName "g") (.expr dt .read))))))))
        | .idx n dt index array => con array
                                       (mkLam (.fn (.expr (.array n dt) .read) .comm) (mkName "e") (.expr (.array n dt) .read)
                                              (con index
                                                   (mkLam (.fn index.type .comm) (mkName "i") index.type
                                                          (applyCon C
                                                                    (mkIdx n dt
                                                                           (mkBvar 0 (mkName "i") index.type)
                                                                           (mkBvar 1 (mkName "e") (.expr (.array n dt) .read)))))))
        | .indexAsNat n e => con e (mkLam (.fn (.expr (.index n) .read) .comm) (mkName "x") (.expr (.index n) .read)
                                          (applyCon C (mkIndexAsNat n (mkBvar 0 (mkName "x") (.expr (.index n) .read)))))
        | .join n m dt a array => con array
                                      (mkLam (.fn (.expr (.array n (.array m dt)) .read) .comm) (mkName "x") (.expr (.array n (.array m dt)) .read)
                                             (applyCon C
                                                       (mkJoin n m dt a (mkBvar 0 (mkName "x") (.expr (.array n (.array m dt)) .read)))))
        | .rlet _ _ _ val f => con  val
                                        (mkLam  (.fn val.type .comm) (mkName "x") val.type
                                                (con (applyCon f (mkBvar 0 (mkName "x") val.type)) C))
        | .makePair dt1 dt2 a fst snd => con fst
                                             (mkLam (.fn (.expr dt1 .read)  .comm) (mkName "x") (.expr dt1 .read)
                                                    (con snd
                                                         (mkLam (.fn (.expr dt2 .read) .comm) (mkName "y") (.expr dt2 .read)
                                                                (applyCon C (mkMakePair dt1 dt2 a
                                                                                        (mkBvar 1 (mkName "x") (.expr dt1 .read))
                                                                                        (mkBvar 0 (mkName "y") (.expr dt2 .read)))))))
        | .map n dt1 dt2 _ f array  => con  array
                                            (mkLam  (.fn (.expr (.array n dt1) .read) .comm) (mkName "x") (.expr (.array n dt1) .read)
                                                    (applyCon   C
                                                                (mkMapRead n dt1 dt2
                                                                        (mkLam (.fn (.expr dt1 .read) .comm) (mkName "a") (.expr dt1 .read)
                                                                                (mkLam (.fn (.fn (.expr dt2 .read) .comm) .comm) (mkName "cont") (.fn (.expr dt2 .read) .comm)
                                                                                        (con (applyCon f
                                                                                                        (mkBvar 1 (mkName "a") (.expr dt1 .read)))
                                                                                            (mkLam (.fn (.expr dt2 .read) .comm) (mkName "b") (.expr dt2 .read)
                                                                                                    (mkApp .comm
                                                                                                            (mkBvar 1 (mkName "cont") (.fn (.expr dt2 .read) .comm))
                                                                                                            (mkBvar 0 (mkName "b") (.expr dt2 .read)))))))
                                                                        (mkBvar 0 (mkName "x") (.expr (.array n dt1) .read)))))
        | .mapFst dt1 dt2 dt3 a f record => con record
                                                (mkLam  (.fn record.type .comm) (mkName "x") record.type
                                                        (applyCon C
                                                                  (mkMapFst dt1 dt2 dt3 a f (mkBvar 0 (mkName "x") record.type))))
        | .mapSeq _ n _ dt _ _ => mkNew (.array n dt) (mkLam (.fn (.phrasePair (.expr dt .read) (.acc dt)) .comm) (mkName "tmp") (.phrasePair (.expr dt .read) (.acc dt))
                                                             (mkSeq (acc {node := .functional func, type :=type}
                                                                         {node := .proj2 (mkBvar 0 (mkName "tmp") (.phrasePair (.expr dt .read) (.acc dt))), type := (.acc dt)})
                                                                    (applyCon C
                                                                              {node := .proj1 (mkBvar 0 (mkName "tmp") (.phrasePair (.expr dt .read) (.acc dt))), type := (.expr dt .read)})))
        | .mapSnd dt1 dt2 dt3 a f record => con record
                                                (mkLam  (.fn record.type .comm) (mkName "x") record.type
                                                        (applyCon C
                                                                  (mkMapSnd dt1 dt2 dt3 a f (mkBvar 0 (mkName "x") record.type))))
        | _ => tbc

-- partial def imperativeCon (imp : ImperativePr imitives) (type : PhraseType) (C: DPIAPhrase) : DPIAPhrase :=
--     match imp with
--         | _ => tbc

end
