import DPIA.Substitutions
import DPIA.mkFunctions

private abbrev HashSeen := Std.HashMap (Lean.Name × Nat) (Lean.Name × Nat) -- set or list would be sufficient, i do not use the value only check if key is in it


-- increments the index of a DPIAPhrase identifier of an
-- outer function definition if a function was added
partial def adjustIndex (p : DPIAPhrase) (seenFn : Nat) (ids : HashSeen) (depth : Nat): DPIAPhrase :=
    match p.node with
        | .bvar idx name => match ids.get? (name, (depth- idx-1)) with
                                        | some _ => p
                                        | none => {node := .bvar (idx + seenFn) name, type := p.type}
        | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => adjustIndex x seenFn ids depth) (fun x => x) (fun x => x)), type := p.type}
        | .functional func => {node := .functional (substituteInFunctional func (fun x => adjustIndex x seenFn ids depth) (fun x => x) (fun x => x)), type := p.type}
        | .lit _ => p
        | .app fn arg => {node := .app (adjustIndex fn seenFn ids depth) (adjustIndex arg seenFn ids depth), type := p.type}
        | .depapp fn arg => {node := .depapp (adjustIndex fn seenFn ids depth) arg, type := p.type}
        | .lam name type body => {node := .lam name type (adjustIndex body seenFn (ids.insert (name, depth) (name, depth)) (depth+1)), type := p.type}
        | .deplam name kind body => {node := .deplam name kind (adjustIndex body seenFn ids depth), type := p.type}
        | .pair fst snd => {node := .pair (adjustIndex fst seenFn ids depth) (adjustIndex snd seenFn ids depth), type := p.type}
        | .proj1 p => {node := .proj1 (adjustIndex p seenFn ids depth), type := p.type}
        | .proj2 p => {node := .proj2 (adjustIndex p seenFn ids depth), type := p.type}
        | .ifThenElse cond thenP elseP => {node := .ifThenElse (adjustIndex cond seenFn ids depth) (adjustIndex thenP seenFn ids depth) (adjustIndex elseP seenFn ids depth), type := p.type}
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
                                        | none => mkBvar (idx + depth-1) userName In.type
    | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => reductionHelper phrase x For depth ids) (fun x => x) (fun x => x)), type := In.type}
    | .functional func => {node := .functional (substituteInFunctional func (fun x => reductionHelper phrase x For depth ids) (fun x => x) (fun x => x)), type := In.type}
    | .lit _ => In
    | .app fn arg => let sFn := reductionHelper phrase fn For depth ids
                     let sArg := reductionHelper phrase arg For depth ids
                     {node := .app sFn sArg, type := In.type : DPIAPhrase}
    | .depapp fn arg => let sFn := reductionHelper phrase fn For depth ids
                        {node := .depapp sFn arg, type := In.type : DPIAPhrase}
    | .lam binderName binderType body =>  let sBody := reductionHelper phrase body For (depth+1) (ids.insert (binderName, depth) (binderName, depth))
                                          {node := .lam binderName binderType sBody, type := In.type}
    | .deplam binderName binderKind body => let sBody := reductionHelper phrase body For depth ids
                                            {node := .deplam binderName binderKind sBody, type := In.type : DPIAPhrase}
    | .pair fst snd =>  let sFst := reductionHelper phrase fst For depth ids
                        let sSnd := reductionHelper phrase snd For depth ids
                        {node := .pair sFst sSnd, type := In.type : DPIAPhrase}
    | .proj1 p => let sP := reductionHelper phrase p For depth ids
                  {node := .proj1 sP, type := In.type : DPIAPhrase}
    | .proj2 p => let sP := reductionHelper phrase p For depth ids
                  {node := .proj1 sP, type := In.type : DPIAPhrase}
    | .ifThenElse cond thenP elseP => let sCond := reductionHelper phrase cond For depth ids
                                      let sThenP := reductionHelper phrase thenP For depth ids
                                      let sElseP := reductionHelper phrase elseP For depth ids
                                      {node := .ifThenElse sCond sThenP sElseP, type := In.type : DPIAPhrase}
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
        | .array n aDt => RData.array n (reduceDataInData dt For aDt depth ids)
        | .pair p1 p2 => RData.pair (reduceDataInData dt For p1 depth ids) (reduceDataInData dt For p2 depth ids)
        | .index _ => In
        | .scalar _ => In
        | .natType => In
        | .vector n vDt => RData.vector n (reduceDataInData dt For vDt depth ids)
        | _ => panic! s!"that should never happen"

-- in PhraseTypes
def reduceDataInPt (sN : RData) (For : Lean.Name) (In : PhraseType) (depth : Nat) (ids : HashSeen): PhraseType :=
    match In with
        | .expr dt rw => let nDt := reduceDataInData sN For dt depth ids
                         .expr nDt rw
        | .comm => In
        | .acc dt => let nDt := reduceDataInData sN For dt depth ids
                     .acc nDt
        | .pi binderKind userName body => let nBody := reduceDataInPt sN For body (depth +1) ids
                                          .pi binderKind userName nBody
        | .fn binderType body => let nBinderType := reduceDataInPt sN For binderType depth ids
                                 let nBody := reduceDataInPt sN For body depth ids
                                 .fn nBinderType nBody
        | .phrasePair p1 p2 => let nP1 := reduceDataInPt sN For p1 depth ids
                               let nP2 := reduceDataInPt sN For p2 depth ids
                               .phrasePair nP1 nP2

----------------- reduce Nat -----------------

-- in Data
def reduceNatInData (n : RNat) (For : Lean.Name) (In : RData) (depth : Nat) (ids : HashSeen) : RData :=
  match In with
    | .bvar idx name => if name.toString == For.toString && depth == idx then RData.natType
                            else match ids.get? (name, (depth- idx)) with
                                    | some _ => In
                                    | none => .bvar (idx-1) name
    | .array n aDt => RData.array n (reduceNatInData n For aDt depth ids)
    | .pair p1 p2 => RData.pair (reduceNatInData n For p1 depth ids) (reduceNatInData n For p2 depth ids)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => RData.vector n (reduceNatInData n For vDt depth ids)
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
    | .expr dt rw => let nDt := reduceNatInData sN For dt depth ids
                    PhraseType.expr nDt rw
    | .comm => In
    | .acc dt => let nDt := reduceNatInData sN For dt depth ids
                PhraseType.acc nDt
    | .pi binderKind userName body => let nBody := reduceNatInPt sN For body (depth +1) ids
                                     PhraseType.pi binderKind userName nBody
    | .fn binderType body => let nBinderType := reduceNatInPt sN For binderType depth ids
                            let nBody := reduceNatInPt sN For body depth ids
                            PhraseType.fn nBinderType nBody
    | .phrasePair p1 p2 => let nP1 := reduceNatInPt sN For p1 depth ids
                          let nP2 := reduceNatInPt sN For p2 depth ids
                          PhraseType.phrasePair nP1 nP2



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

-- i used a hash map because i thought would be more efficient
partial def depReductionHelper (w : DWrapper) (In : DPIAPhrase) (For : Lean.Name) (depth : Nat) (ids : HashSeen): DPIAPhrase :=
    let type := reduceDWrapperPt w In.type For depth ids
    let node := match In.node with
                | .bvar _ _ => In.node
                | .imperative imp => .imperative (substituteInImperative imp (fun x => depReductionHelper w x For depth ids)
                                                                             (fun x => reduceDWrapperD w x For depth ids)
                                                                             (fun x => reduceDWrapperN w x For depth ids))
                | .functional func => .functional (substituteInFunctional func (fun x => depReductionHelper w x For depth ids)
                                                                               (fun x => reduceDWrapperD w x For depth ids)
                                                                               (fun x => reduceDWrapperN w x For depth ids))
                | .lit _ => In.node
                | .app fn arg => let sFn := depReductionHelper w fn For depth ids
                                let sArg := depReductionHelper w arg For depth ids
                                .app sFn sArg
                | .depapp fn arg => let sFn := depReductionHelper w fn For depth ids
                                    .depapp sFn arg
                | .lam binderName binderType body => let sBody := depReductionHelper w body For depth ids
                                                     let sType := reduceDWrapperPt w binderType For depth ids
                                                     .lam binderName sType sBody
                | .deplam binderName binderKind body => let sBody := depReductionHelper w body For (depth+1) (ids.insert (binderName, depth) (binderName, depth))
                                                        .deplam binderName binderKind sBody
                | .pair fst snd =>  let sFst := depReductionHelper w fst For depth ids
                                    let sSnd := depReductionHelper w snd For depth ids
                                    .pair sFst sSnd
                | .proj1 p => let sP := depReductionHelper w p For depth ids
                              .proj1 sP
                | .proj2 p => let sP := depReductionHelper w p For depth ids
                              .proj1 sP
                | .ifThenElse cond thenP elseP =>   let sCond := depReductionHelper w cond For depth ids
                                                    let sThenP := depReductionHelper w thenP For depth ids
                                                    let sElseP := depReductionHelper w elseP For depth ids
                                                    .ifThenElse sCond sThenP sElseP
                | .natural _ => In.node
    {node := node, type := type}

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
        | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => reduction x) (fun x => x) (fun x => x)), type := phrase.type}
        | .functional prim => {node := .functional (substituteInFunctional prim (fun x => reduction x) (fun x => x) (fun x => x)), type := phrase.type}
        | .lit _ => phrase
        | .app fn arg => reduction (betaReduction fn arg)
        | .depapp fn arg => reduction (dependentBetaReduction fn arg)
        | .lam binderName binderType body => {node := .lam binderName binderType (reduction body), type := phrase.type}
        | .deplam binderName binderKind body => {node := .deplam binderName binderKind (reduction body), type := phrase.type}
        | .pair fst snd => {node := .pair (reduction fst) (reduction snd), type := phrase.type}
        | .proj1 p => {node := .proj1 (reduction p), type := phrase.type}
        | .proj2 p => {node := .proj1 (reduction p), type := phrase.type}
        | .ifThenElse cond thenP elseP => {node := .ifThenElse (reduction cond) (reduction thenP) (reduction elseP), type := phrase.type}
        | .natural _ => phrase
end
