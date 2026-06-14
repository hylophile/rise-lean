import DPIA.Substitutions
import DPIA.mkFunctions

private abbrev HashSeen := Std.HashSet (Lean.Name × Nat)


-- increments the index of a DPIAPhrase identifier of an
-- outer function definition if a function was added
partial def adjustIndex (p : DPIAPhrase) (seenFn : Nat) (ids : HashSeen) (depth : Nat): DPIAPhrase :=
    match p.node with
        | .bvar idx name => match ids.get? (name, (depth- idx-1)) with
                                        | some _ => p
                                        | none => mkBvar (idx + seenFn) name p.type
        | .imperative imp => mkImperative p.type (substituteInImperative imp (fun x => adjustIndex x seenFn ids depth) (fun x => x) (fun x => x))
        | .functional func => mkFunctional p.type (substituteInFunctional func (fun x => adjustIndex x seenFn ids depth) (fun x => x) (fun x => x))
        | .lit _ => p
        | .app fn arg => mkApp p.type (adjustIndex fn seenFn ids depth)
                                      (adjustIndex arg seenFn ids depth)
        | .depapp fn arg => mkDepApp p.type (adjustIndex fn seenFn ids depth) arg
        | .lam name type body => mkLam p.type name type (adjustIndex body seenFn (ids.insert (name, depth)) (depth+1))
        | .deplam name kind body => mkDeplam p.type name kind (adjustIndex body seenFn ids depth)
        | .pair fst snd => mkPair p.type (adjustIndex fst seenFn ids depth) (adjustIndex snd seenFn ids depth)
        | .proj1 p => mkProj1 p.type (adjustIndex p seenFn ids depth)
        | .proj2 p => mkProj2 p.type (adjustIndex p seenFn ids depth)
        | .ifThenElse cond thenP elseP => mkIfThenElse p.type (adjustIndex cond seenFn ids depth)
                                                              (adjustIndex thenP seenFn ids depth)
                                                              (adjustIndex elseP seenFn ids depth)
        | .natural _ => p

-------------------- simple reduction ------------------------
partial def reductionHelper (phrase In : DPIAPhrase) (For : Lean.Name) (depth : Nat) (ids : HashSeen) : DPIAPhrase :=
  match In.node with
    | .bvar idx userName => if userName == For && idx == depth
                                then match phrase.node with
                                        | .bvar i name => mkBvar (idx+i) name phrase.type
                                        | _ => adjustIndex phrase depth {} 0
                                else match ids.get? (userName, (depth- idx-1)) with
                                        | some _ => In
                                        | none => mkBvar (idx-1) userName In.type --mkBvar (idx + depth-1) userName In.type
    | .imperative imp => mkImperative In.type (substituteInImperative imp (fun x => reductionHelper phrase x For depth ids) (fun x => x) (fun x => x))
    | .functional func => mkFunctional In.type (substituteInFunctional func (fun x => reductionHelper phrase x For depth ids) (fun x => x) (fun x => x))
    | .lit _ => In
    | .app fn arg => mkApp In.type  (reductionHelper phrase fn For depth ids)
                                    (reductionHelper phrase arg For depth ids)
    | .depapp fn arg => mkDepApp In.type (reductionHelper phrase fn For depth ids) arg
    | .lam binderName binderType body =>  mkLam In.type binderName binderType (reductionHelper phrase body For (depth+1) (ids.insert (binderName, depth)))
    | .deplam binderName binderKind body => mkDeplam In.type binderName binderKind (reductionHelper phrase body For depth ids)
    | .pair fst snd =>  mkPair In.type (reductionHelper phrase fst For depth ids)
                                       (reductionHelper phrase snd For depth ids)
    | .proj1 p => mkProj1 In.type (reductionHelper phrase p For depth ids)
    | .proj2 p => mkProj2 In.type (reductionHelper phrase p For depth ids)
    | .ifThenElse cond thenP elseP => mkIfThenElse In.type (reductionHelper phrase cond For depth ids)
                                                           (reductionHelper phrase thenP For depth ids)
                                                           (reductionHelper phrase elseP For depth ids)
    | .natural _ => In

def reduce (phrase In : DPIAPhrase) (For : Lean.Name): DPIAPhrase :=
   reductionHelper phrase In For 0 {}


-------------- dependent reduction -------------------------

-- increments the index of a Nat identifier of an
-- outer function definition if a function was eliminated
def adjustIndexNat (num: RNat) (seenFn : Nat) (ids : HashSeen) (depth : Nat) : RNat :=
    match num with
        | .bvar idx name => match ids.get? (name, (depth- idx-1)) with
                                        | some _ => num
                                        | none => .bvar (idx + seenFn) name
        | .nat _ => num
        | .plus n m => .plus (adjustIndexNat n seenFn ids depth) (adjustIndexNat m seenFn ids depth)
        | .minus n m => .minus (adjustIndexNat n seenFn ids depth) (adjustIndexNat m seenFn ids depth)
        | .mult n m => .mult (adjustIndexNat n seenFn ids depth) (adjustIndexNat m seenFn ids depth)
        | .div n m => .div (adjustIndexNat n seenFn ids depth) (adjustIndexNat m seenFn ids depth)
        | .pow n m => .pow (adjustIndexNat n seenFn ids depth) (adjustIndexNat m seenFn ids depth)
        | _ => panic! s!"there should not be any mvars anymore"

-- increments the index of a data identifier of an
-- outer function definition if a function was eliminated
def adjustIndexData (dt: RData) (seenFn : Nat) (ids : HashSeen) (depth : Nat) : RData :=
    match dt with
        | .bvar idx name =>  match ids.get? (name, (depth- idx-1)) with
                                        | some _ => dt
                                        | none => .bvar (idx + seenFn) name
        | .array n aDt => .array n (adjustIndexData aDt seenFn ids depth)
        | .pair p1 p2 => .pair (adjustIndexData p1 seenFn ids depth) (adjustIndexData p2 seenFn ids depth)
        | .index _ => dt
        | .scalar _ => dt
        | .natType => dt
        | .vector n vDt => RData.vector n (adjustIndexData vDt seenFn ids depth)
        | _ => panic! s!"that should never happen"

---------------------- reduce Data ------------------

--in Data
def reduceDataInData (dt : RData) (For : Lean.Name) (In : RData) (depth : Nat) (ids : HashSeen): RData :=
    match In with
        | .bvar idx name => if name.toString == For.toString && depth == idx
                                then match dt with
                                                | .bvar i n => .bvar (idx+i) n
                                                | _ => adjustIndexData dt depth {} 0
                                else match ids.get? (name, (depth- idx)) with
                                        | some _ => In
                                        | none => .bvar (idx + depth -1) name
        | .array n aDt => .array n (reduceDataInData dt For aDt depth ids)
        | .pair p1 p2 => .pair (reduceDataInData dt For p1 depth ids) (reduceDataInData dt For p2 depth ids)
        | .index _ => In
        | .scalar _ => In
        | .natType => In
        | .vector n vDt => .vector n (reduceDataInData dt For vDt depth ids)
        | _ => panic! s!"that should never happen"

-- in PhraseTypes
def reduceDataInPt (sN : RData) (For : Lean.Name) (In : PhraseType) (depth : Nat) (ids : HashSeen): PhraseType :=
    match In with
        | .expr dt rw => .expr (reduceDataInData sN For dt depth ids) rw
        | .comm => In
        | .acc dt => .acc (reduceDataInData sN For dt depth ids)
        | .pi binderKind userName body => .pi binderKind userName (reduceDataInPt sN For body (depth +1) ids)
        | .fn binderType body => .fn (reduceDataInPt sN For binderType depth ids) (reduceDataInPt sN For body depth ids)
        | .phrasePair p1 p2 => .phrasePair (reduceDataInPt sN For p1 depth ids) (reduceDataInPt sN For p2 depth ids)

----------------- reduce Nat -----------------

-- in Data
def reduceNatInData (n : RNat) (For : Lean.Name) (In : RData) (depth : Nat) (ids : HashSeen) : RData :=
  match In with
    | .bvar idx name => if name.toString == For.toString && depth == idx then .natType
                            else match ids.get? (name, (depth- idx)) with
                                    | some _ => In
                                    | none => .bvar (idx-1) name
    | .array n aDt => .array n (reduceNatInData n For aDt depth ids)
    | .pair p1 p2 => .pair (reduceNatInData n For p1 depth ids) (reduceNatInData n For p2 depth ids)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => .vector n (reduceNatInData n For vDt depth ids)
    | _ => panic! s!"that should never happen"

-- in Nat
partial def reduceNatInNat (num: RNat) (For : Lean.Name) (In: RNat) (depth : Nat) (ids : HashSeen) : RNat :=
  match In with
    | .bvar idx name => if name.toString == For.toString && depth == idx
                        then match num with
                                | .bvar i n => .bvar (idx +i) n
                                | _ => adjustIndexNat num depth {} 0
                        else match ids.get? (name, (depth- idx)) with
                                            | some _ => In
                                            | none => .bvar (idx-1) name
    | .nat _ => In
    | .plus n m => .plus (reduceNatInNat n For In depth ids) (reduceNatInNat m For In depth ids)
    | .minus n m => .minus (reduceNatInNat n For In depth ids) (reduceNatInNat m For In depth ids)
    | .mult n m => .mult (reduceNatInNat n For In depth ids) (reduceNatInNat m For In depth ids)
    | .div n m => .div (reduceNatInNat n For In depth ids) (reduceNatInNat m For In depth ids)
    | .pow n m => .pow (reduceNatInNat n For In depth ids) (reduceNatInNat m For In depth ids)
    | _ => panic! s!"there should not be any mvars anymore"

-- in PhraseTypes
def reduceNatInPt (sN : RNat) (For : Lean.Name) (In : PhraseType) (depth : Nat) (ids : HashSeen) : PhraseType :=
  match In with
    | .expr dt rw => .expr (reduceNatInData sN For dt depth ids) rw
    | .comm => In
    | .acc dt => .acc (reduceNatInData sN For dt depth ids)
    | .pi binderKind userName body => .pi binderKind userName (reduceNatInPt sN For body (depth +1) ids)
    | .fn binderType body => .fn (reduceNatInPt sN For binderType depth ids)
                                 (reduceNatInPt sN For body depth ids)
    | .phrasePair p1 p2 => .phrasePair (reduceNatInPt sN For p1 depth ids) (reduceNatInPt sN For p2 depth ids)



-- in PhraseTypes
def reduceDWrapperPt (depArg : DWrapper) (In : PhraseType) (For : Lean.Name) (depth : Nat) (ids : HashSeen): PhraseType:=
  match depArg with
    | .rise (.nat n) => reduceNatInPt n For In depth ids
    | .rise (.data d) => reduceDataInPt d For In depth ids
    | _ => panic! s!"other wrapper types but nat data and readwrite are not implemented yet"

-- in Data
def reduceDWrapperD (depArg : DWrapper) (In : RData) (For : Lean.Name) (depth : Nat) (ids : HashSeen): RData :=
  match depArg with
    | .rise (.nat n) => reduceNatInData n For In depth ids
    | .rise (.data d) => reduceDataInData d For In depth ids
    | _ => panic! s!"other wrapper types but nat data and readwrite are not implemented yet"

-- in Nat
def reduceDWrapperN (depArg : DWrapper) (In : RNat) (For : Lean.Name) (depth : Nat) (ids : HashSeen): RNat :=
  match depArg with
    | .rise (.nat n) => reduceNatInNat n For In depth ids
    | .rise (.data _) =>  panic! s!"it is not possible to substitute data in nat"
    | _ => panic! s!"other wrapper types but nat data and readwrite are not implemented yet"


partial def depReductionHelper (w : DWrapper) (In : DPIAPhrase) (For : Lean.Name) (depth : Nat) (ids : HashSeen): DPIAPhrase :=
    let type := reduceDWrapperPt w In.type For depth ids
    match In.node with
                | .bvar _ _ => {node := In.node, type := type}
                | .imperative imp => mkImperative type (substituteInImperative imp (fun x => depReductionHelper w x For depth ids)
                                                                                   (fun x => reduceDWrapperD w x For depth ids)
                                                                                   (fun x => reduceDWrapperN w x For depth ids))
                | .functional func => mkFunctional type (substituteInFunctional func (fun x => depReductionHelper w x For depth ids)
                                                                                     (fun x => reduceDWrapperD w x For depth ids)
                                                                                     (fun x => reduceDWrapperN w x For depth ids))
                | .lit _ => {node := In.node, type := type}
                | .app fn arg => mkApp type (depReductionHelper w fn For depth ids) (depReductionHelper w arg For depth ids)
                | .depapp fn arg => mkDepApp type (depReductionHelper w fn For depth ids) arg
                | .lam binderName binderType body => mkLam type binderName (reduceDWrapperPt w binderType For depth ids)
                                                                           (depReductionHelper w body For depth ids)
                | .deplam binderName binderKind body => mkDeplam type binderName binderKind (depReductionHelper w body For (depth+1) (ids.insert (binderName, depth)))
                | .pair fst snd => mkPair type (depReductionHelper w fst For depth ids) (depReductionHelper w snd For depth ids)
                | .proj1 p => mkProj1 type (depReductionHelper w p For depth ids)
                | .proj2 p => mkProj2 type (depReductionHelper w p For depth ids)
                | .ifThenElse cond thenP elseP => mkIfThenElse type (depReductionHelper w cond For depth ids)
                                                                    (depReductionHelper w thenP For depth ids)
                                                                    (depReductionHelper w elseP For depth ids)
                | .natural _ => {node := In.node, type := type}

def depReduce (arg : DWrapper) (In : DPIAPhrase) (For : Lean.Name): DPIAPhrase :=
   depReductionHelper arg In For 0 {}

mutual

-- handles a specific apply
partial def betaReduction (In phrase : DPIAPhrase) : DPIAPhrase :=
    match In.node with
        | .lam name _ body => reduce phrase body name
        | .app fn arg => let sFn := betaReduction fn arg
                         match sFn.node with
                            | .lam name _ body => reduce phrase body name
                            | _ => panic! s!"the first argument of an apply needs to be a function but is {sFn}"
        | .depapp fn arg => let sFn := dependentBetaReduction fn arg
                            match sFn.node with
                                | .lam name _ body => reduce phrase body name
                                | _ => panic! s!"the first argument of an dependent apply needs to be a function but is {sFn}"
        | _ => panic! s!"{In.node} is not valid function"

-- handles a specific dependent apply
partial def dependentBetaReduction (In : DPIAPhrase) (depArg : DWrapper): DPIAPhrase :=
    match In.node with
                | .app fn arg => let sFn := betaReduction fn arg
                                match sFn.node with
                                    | .deplam name _ body => depReduce depArg body name
                                    | _ => panic! s!"the first argument of an apply needs to be a dependent function but is {sFn}"
                | .depapp fn arg => let sFn := dependentBetaReduction fn arg
                                    match sFn.node with
                                        | .deplam name _ body => depReduce depArg body name
                                        | _ => panic! s!"the first argument of an dependent apply needs to be a dependent function but is {sFn}"
                | .deplam name _ body => depReduce depArg body name
                | _ => panic! s!"{In.node} is not valid dependent function"


-- reduces all apps and depapps in a DPIAPhrase
partial def reduction (phrase : DPIAPhrase) : DPIAPhrase :=
    match phrase.node with
        | .bvar .. => phrase
        | .imperative imp => mkImperative phrase.type (substituteInImperative imp (fun x => reduction x) (fun x => x) (fun x => x))
        | .functional prim => mkFunctional phrase.type (substituteInFunctional prim (fun x => reduction x) (fun x => x) (fun x => x))
        | .lit _ => phrase
        | .app fn arg => reduction (betaReduction fn arg)
        | .depapp fn arg => reduction (dependentBetaReduction fn arg)
        | .lam binderName binderType body => mkLam phrase.type binderName binderType (reduction body)
        | .deplam binderName binderKind body => mkDeplam phrase.type binderName binderKind (reduction body)
        | .pair fst snd => mkPair phrase.type (reduction fst) (reduction snd)
        | .proj1 p => mkProj1 phrase.type (reduction p)
        | .proj2 p => mkProj2 phrase.type (reduction p)
        | .ifThenElse cond thenP elseP => mkIfThenElse phrase.type (reduction cond) (reduction thenP) (reduction elseP)
        | .natural _ => phrase
end
