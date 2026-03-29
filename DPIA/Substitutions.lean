import DPIA.Basic
import Rise.Basic

-- hopefully I will be able to reuse it
def substituteInFunctional (In : FunctionalPrimitives) (phraseFn : DPIAPhrase → DPIAPhrase) (dataFn : RData → RData) (natFn : RNat → RNat): FunctionalPrimitives :=
  match In with
    | .id val => .id (phraseFn val)
    | .neg val => .neg (phraseFn val)
    | .add lhs rhs => .add (phraseFn lhs) (phraseFn rhs)
    | .sub lhs rhs => .sub (phraseFn lhs) (phraseFn rhs)
    | .mul lhs rhs => .mul (phraseFn lhs) (phraseFn rhs)
    | .div lhs rhs => .div  (phraseFn lhs) (phraseFn rhs)
    | .mod lhs rhs => .mod (phraseFn lhs) (phraseFn rhs)
    | .not val => .not (phraseFn val)
    | .gt lhs rhs => .gt (phraseFn lhs) (phraseFn rhs)
    | .lt lhs rhs => .lt (phraseFn lhs) (phraseFn rhs)
    | .equal lhs rhs => .equal (phraseFn lhs) (phraseFn rhs)
    | .cast s t x => .cast (dataFn s) (dataFn t) (phraseFn x)
    | .indexAsNat n idx => .indexAsNat (natFn n) (phraseFn idx)
    | .natAsIndex n idx => .natAsIndex (natFn n) (phraseFn idx)
    | .rlet s t a f val => .rlet (dataFn s) (dataFn t) a (phraseFn f) (phraseFn val)
    | .toMem t input => .toMem (dataFn t) (phraseFn input)
    | .generate n t f  => .generate (natFn n) (dataFn t) (phraseFn f)
    | .idx n t idx array => .idx (natFn n) (dataFn t) (phraseFn idx) (phraseFn array)
    | .depIdx ..  => In -- needs to be fixed at some point
    | .idxVec n t idx vec  => .idxVec (natFn n) (dataFn t) (phraseFn idx) (phraseFn vec)
    | .take n m t array => .take (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .drop n m t array => .drop (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .concat n m t nArray mArray => .concat (natFn n) (natFn m) (dataFn t) (phraseFn nArray) (phraseFn mArray)
    | .split n m t a array => .split (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .join n m t a array => .join (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .depJoin .. => In  -- needs to be fixed at some point
    | .slide n sz sp t array => .slide (natFn n) (natFn sz) (natFn sp) (dataFn t) (phraseFn array)
    | .circularBuffer n alloc sz s t load array => .circularBuffer (natFn n) (natFn alloc) (natFn sz) (dataFn s) (dataFn t) (phraseFn load) (phraseFn array)
    | .rotateValues n sz t wrt array => .rotateValues (natFn n) (natFn sz) (dataFn t) wrt (phraseFn array)
    | .transpose n m t a array => .transpose (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .cycle n m  t array  => .cycle (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .reorder .. =>  In  -- needs to be fixed at some point
    | .transposeDepArray .. =>  In  -- needs to be fixed at some point
    | .gather n m t idx array => .gather (natFn n) (natFn m) (dataFn t) (phraseFn idx) (phraseFn array)
    | .scatter n m t idx array => .scatter (natFn n) (natFn m) (dataFn t) (phraseFn idx) (phraseFn array)
    | .padCst n l r t padExpr array => .padCst (natFn n) (natFn l) (natFn r) (dataFn t) (phraseFn padExpr) (phraseFn array)
    | .padClamp n l r t array => .padClamp (natFn n) (natFn l) (natFn r) (dataFn t) (phraseFn array)
    | .padEmpty n r t array => .padEmpty (natFn n) (natFn r) (dataFn t) (phraseFn array)
    | .zip n s t a sArray tArray => .zip (natFn n) (dataFn s) (dataFn t) a (phraseFn sArray) (phraseFn tArray)
    | .unzip n s t a array  => .unzip (natFn n) (dataFn s) (dataFn t) a (phraseFn array)
    | .depZip ..  =>  In  -- needs to be fixed at some point
    | .partition .. =>  In  -- needs to be fixed at some point
    | .makePair s t a fst snd  => .makePair (dataFn s) (dataFn t) a (phraseFn fst) (phraseFn snd)
    | .fst s t pair => .fst (dataFn s) (dataFn t) (phraseFn pair)
    | .snd s t pair => .snd (dataFn s) (dataFn t) (phraseFn pair)
    | .vectorFromScalar n t arg  => .vectorFromScalar (natFn n) (dataFn t) (phraseFn arg)
    | .asVector n m t a array  => .asVector (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .asVectorAligned n m t a array  => .asVectorAligned (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .asScalar n m t a array => .asScalar (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .map n s t a f array => .map (natFn n) (dataFn s) (dataFn t) a (phraseFn f) (phraseFn array)
    | .mapSeq unroll n s t f array => .mapSeq unroll (natFn n) (dataFn s) (dataFn t) (phraseFn f) (phraseFn array)
    | .mapStream n s t f array  => .mapStream (natFn n) (dataFn s) (dataFn t) (phraseFn f) (phraseFn array)
    | .iterateStream n s t f array => .iterateStream (natFn n) (dataFn s) (dataFn t) (phraseFn f) (phraseFn array)
    | .depMapSeq .. =>  In  -- needs to be fixed at some point
    | .mapVec n t1 t2 f vec  => .mapVec (natFn n) (dataFn t1) (dataFn t2) (phraseFn f) (phraseFn vec)
    | .mapFst s1 t s2 a f pair => .mapFst (dataFn s1) (dataFn t) (dataFn s2) a (phraseFn f) (phraseFn pair)
    | .mapSnd s t1 t2 a f pair => .mapSnd (dataFn s) (dataFn t1) (dataFn t2) a (phraseFn f) (phraseFn pair)
    | .reduceSeq unroll n  s t f init array  => .reduceSeq unroll (natFn n) (dataFn s) (dataFn t) (phraseFn f) (phraseFn init) (phraseFn array)
    | .scanSeq n s t f init array => .scanSeq (natFn n) (dataFn s) (dataFn t) (phraseFn f) (phraseFn init) (phraseFn array)
    | .iterate n m k t f array => .iterate (natFn n) (natFn m) (natFn k) (dataFn t) (phraseFn f) (phraseFn array)
    | .depTile n tileSize haloSize t1 t2 processTiles array  => .depTile (natFn n) (natFn tileSize) (natFn haloSize) (dataFn t1) (dataFn t2) (phraseFn processTiles) (phraseFn array)
    | .printType msg t a input  => .printType msg (dataFn t) a (phraseFn input)


-- hopefully I will be able to reuse it
def substituteInImperative (In : ImperativePrimitives) (phraseFn : DPIAPhrase → DPIAPhrase) (dataFn  : RData → RData)  (natFn : RNat → RNat): ImperativePrimitives :=
  match In with
    | .asScalarAcc n m t array => .asScalarAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .assign t lhs rhs => .assign (dataFn t) (phraseFn lhs) (phraseFn rhs)
    | .asVectorAcc n m t array => .asVectorAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .forLoop unroll n body  => .forLoop unroll (natFn n) (phraseFn body)
    | .forNat unroll n body => .forNat unroll (natFn n) (phraseFn body)
    | .forVec n t out body => .forVec (natFn n) (dataFn t) (phraseFn out) (phraseFn body)
    | .generateCont n t f  => .generateCont (natFn n) (dataFn t) (phraseFn f)
    | .idxAcc n t idx array => .idxAcc (natFn n) (dataFn t) (phraseFn idx) (phraseFn array)
    | .idxVecAcc n t idx vec => .idxVecAcc (natFn n) (dataFn t) (phraseFn idx) (phraseFn vec)
    | .scatterAcc n m t indicies array => .scatterAcc (natFn n) (natFn m) (dataFn t) (phraseFn indicies) (phraseFn array)
    | .splitAcc n m t array => .splitAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .joinAcc n m t array => .joinAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .unzipAcc n t1 t2 array => .unzipAcc (natFn n) (dataFn t1) (dataFn t2) (phraseFn array)
    | .zipAcc1     n t1 t2 array => .zipAcc1 (natFn n) (dataFn t1) (dataFn t2) (phraseFn array)
    | .zipAcc2     n t1 t2 array => .zipAcc2 (natFn n) (dataFn t1) (dataFn t2) (phraseFn array)
    | .transposeAcc n m t array  => .transposeAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .cycleAcc n m t input => .cycleAcc (natFn n) (natFn m) (dataFn t) (phraseFn input)
    | .reorderAcc      .. => In  -- needs to be fixed at some point
    | .dropAcc n m t array => .dropAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .takeAcc n m t array => .takeAcc (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .mapAcc n t1 t2 f array => .mapAcc (natFn n) (dataFn t1) (dataFn t2) (phraseFn f) (phraseFn array)
    | .mapFstAcc t1 t2 t3 f record  => .mapFstAcc (dataFn t1) (dataFn t2) (dataFn t3) (phraseFn f) (phraseFn record)
    | .mapRead n t1 t2 f input => .mapRead (natFn n) (dataFn t1) (dataFn t2) (phraseFn f) (phraseFn input)
    | .mapSndAcc t1 t2 t3 f record => .mapSndAcc (dataFn t1) (dataFn t2) (dataFn t3) (phraseFn f) (phraseFn record)
    | .mkDPairFstl fst a => .mkDPairFstl (natFn fst) (phraseFn a)
    | .mkDPairSndAcc fst sndT a => .mkDPairSndAcc (natFn fst) (dataFn sndT) (phraseFn a)
    | .pairAcc t1 t2 fst snd => .pairAcc (dataFn t1) (dataFn t2) (phraseFn fst)  (phraseFn snd)
    | .pairAcc1 t1 t2 pair => .pairAcc1 (dataFn t1) (dataFn t2) (phraseFn pair)
    | .pairAcc2 t1 t2 pair => .pairAcc2 (dataFn t1) (dataFn t2) (phraseFn pair)
    | .new t f => .new (dataFn t) (phraseFn f)
    | .newDoubleBuffer n t1 t2 t3 input out f => .newDoubleBuffer (natFn n) (dataFn t1) (dataFn t2) (dataFn t3) (phraseFn input) (phraseFn out) (phraseFn f)
    | .comment _ => In
    | .skip => In
    | .depIdxAcc .. => In  -- needs to be fixed at some point
    | .depJoinAcc .. => In  -- needs to be fixed at some point
    | .dMatchI x elemT outT f input => .dMatchI (natFn x) (dataFn elemT) (dataFn outT) (phraseFn f) (phraseFn input)
    | .seq c1 c2 => .seq (phraseFn c1) (phraseFn c2)

def phraseSize (phrase : DPIAPhrase) : Nat :=
  match phrase with
    | ⟨.bvar ..,_⟩ => 1
    | ⟨.imperative _,_⟩ => 1 -- not correkt like this
    | ⟨.functional _,_⟩ => 1 -- not correkt like this
    | ⟨.lit _,_⟩ => 1
    | ⟨.app fn arg,_⟩ => 1 + phraseSize fn + phraseSize arg
    | ⟨.depapp fn _,_⟩ => 1 + phraseSize fn
    | ⟨.lam _ _ body,_⟩ =>  1 + phraseSize body
    | ⟨.deplam _ _ body,_⟩ => 1 + phraseSize body
    | ⟨.pair fst snd,_⟩ =>  1 + phraseSize fst + phraseSize snd
    | ⟨.proj1 p,_⟩ => 1 + phraseSize p
    | ⟨.proj2 p,_⟩ => 1 + phraseSize p
    | ⟨.ifThenElse cond thenP elseP,_⟩ => 1 + phraseSize cond + phraseSize thenP + phraseSize elseP


-- substitute annotations in DAnnotations
def substituteAnnotationA (a : DAnnotation) (name : Lean.Name) (key : DAnnotation) : DAnnotation :=
  match a with
    | .identifier userName => if userName == name then key else a
    | .read => a
    | .write => a

-- substitute annotations in PhraseTypes
def substituteAnnotationPt (pt : PhraseType) (name : Lean.Name) (key : DAnnotation) : PhraseType :=
  match pt with
    | .expr dt rw => PhraseType.expr dt (substituteAnnotationA rw name key)
    | .comm => pt
    | .acc _ => pt
    | .pi binderKind userName body => PhraseType.pi binderKind userName (substituteAnnotationPt body name key)
    | .fn binderType body => PhraseType.fn (substituteAnnotationPt binderType name key) (substituteAnnotationPt body name key)
    | .phrasePair p1 p2 => PhraseType.phrasePair (substituteAnnotationPt p1 name key) (substituteAnnotationPt p2 name key)

def substituteDataInData (dt : RData) (For : Lean.Name) (In : RData) (depth : Nat): RData :=
  match In with
    | .bvar index userName => if userName.toString == For.toString && depth == index
                              then dt
                              else In
    | .array n aDt => RData.array n (substituteDataInData dt For aDt depth)
    | .pair p1 p2 => RData.pair (substituteDataInData dt For p1 depth) (substituteDataInData dt For p2 depth)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => RData.vector n (substituteDataInData dt For vDt depth)
    | _ => panic! s!"that should never happen"

def substituteNatInData (n : RNat) (For : Lean.Name) (In : RData) (depth : Nat): RData :=
  match In with
    | .bvar index userName => if userName.toString == For.toString && depth == index then RData.natType else In
    | .array n aDt => RData.array n (substituteNatInData n For aDt depth)
    | .pair p1 p2 => RData.pair (substituteNatInData n For p1 depth) (substituteNatInData n For p2 depth)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => RData.vector n (substituteNatInData n For vDt depth)
    | _ => panic! s!"that should never happen"


-- def substituteInPhraseType (sM : RData ⊕ RNat) (For : Lean.Name) (In : PhraseType) : PhraseType :=
--   match In with
--     | .expr dt rw => match sM with
--                       | (sD : RData) => let nDt := substituteDataInData sD For dt
--                                         PhraseType.expr nDt rw
--                       | (sN : RNat) => let nDt := substituteNatInData sN For dt
--                                        PhraseType.expr nDt rw
--                       | _ => panic! s!"Type not supportet yet"
--     | .comm => In
--     | .acc dt => let nDt := substituteDataInData sN For dt
--                 PhraseType.acc nDt
--     | .pi binderKind userName body => let nBody := substituteInPhraseType α sN For body
--                                      PhraseType.pi binderKind userName nBody
--     | .fn binderType body => let nBinderType := substituteInPhraseType α sN For binderType
--                             let nBody := substituteInPhraseType α sN For body
--                             PhraseType.fn nBinderType nBody
--     | .phrasePair p1 p2 => let nP1 := substituteInPhraseType α sN For p1
--                           let nP2 := substituteInPhraseType α sN For p2
--                           PhraseType.phrasePair nP1 nP2

def substituteDataInPhraseTypeHelper (sN : RData) (For : Lean.Name) (In : PhraseType) (depth : Nat): PhraseType :=
  match In with
    | .expr dt rw => let nDt := substituteDataInData sN For dt depth
                    PhraseType.expr nDt rw
    | .comm => In
    | .acc dt => let nDt := substituteDataInData sN For dt depth
                PhraseType.acc nDt
    | .pi binderKind userName body => let nBody := substituteDataInPhraseTypeHelper sN For body (depth +1)
                                     PhraseType.pi binderKind userName nBody
    | .fn binderType body => let nBinderType := substituteDataInPhraseTypeHelper sN For binderType depth
                            let nBody := substituteDataInPhraseTypeHelper sN For body depth
                            PhraseType.fn nBinderType nBody
    | .phrasePair p1 p2 => let nP1 := substituteDataInPhraseTypeHelper sN For p1 depth
                          let nP2 := substituteDataInPhraseTypeHelper sN For p2 depth
                          PhraseType.phrasePair nP1 nP2

def substituteDataInPhraseType (sN : RData) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  substituteDataInPhraseTypeHelper sN For In 0

def substituteNatInPhraseTypeHelper (sN : RNat) (For : Lean.Name) (In : PhraseType) (depth : Nat) : PhraseType :=
  match In with
    | .expr dt rw => let nDt := substituteNatInData sN For dt depth
                    PhraseType.expr nDt rw
    | .comm => In
    | .acc dt => let nDt := substituteNatInData sN For dt depth
                PhraseType.acc nDt
    | .pi binderKind userName body => let nBody := substituteNatInPhraseTypeHelper sN For body (depth +1)
                                     PhraseType.pi binderKind userName nBody
    | .fn binderType body => let nBinderType := substituteNatInPhraseTypeHelper sN For binderType depth
                            let nBody := substituteNatInPhraseTypeHelper sN For body depth
                            PhraseType.fn nBinderType nBody
    | .phrasePair p1 p2 => let nP1 := substituteNatInPhraseTypeHelper sN For p1 depth
                          let nP2 := substituteNatInPhraseTypeHelper sN For p2 depth
                          PhraseType.phrasePair nP1 nP2

def substituteNatInPhraseType (sN : RNat) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  substituteNatInPhraseTypeHelper sN For In 0

def substituteNatInRType (sN : RNat) (For : Lean.Name) (In : RType) (depth : Nat) : RType :=
  match In with
    | .data dt => .data (substituteNatInData sN For dt depth)
    | .pi binderKind binderInfo userName body => .pi binderKind binderInfo userName (substituteNatInRType sN For body depth)
    | .fn binderType body => .fn (substituteNatInRType sN For binderType depth) (substituteNatInRType sN For body depth)

def substituteDataInRType (data : RData) (For : Lean.Name) (In : RType) (depth : Nat) : RType :=
  match In with
    | .data dt => .data (substituteDataInData data For dt depth)
    | .pi binderKind binderInfo userName body => .pi binderKind binderInfo userName (substituteDataInRType data For body depth)
    | .fn binderType body => .fn (substituteDataInRType data For binderType depth) (substituteDataInRType data For body depth)

-- for lamdas
partial def substitutePhraseInPhraseHelper (phrase In : DPIAPhrase) (For : Lean.Name) (depth : Nat): DPIAPhrase :=
  match In.node with
    | .bvar deBruijnIndex userName => if userName == For && deBruijnIndex == depth then phrase
                                      else In
    | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => substitutePhraseInPhraseHelper phrase x For depth) (fun x => x) (fun x => x)), type := In.type}
    | .functional func => {node := .functional (substituteInFunctional func (fun x => substitutePhraseInPhraseHelper phrase x For depth) (fun x => x) (fun x => x)), type := In.type}
    | .lit _ => In
    | .app fn arg => let sFn := substitutePhraseInPhraseHelper phrase fn For depth
                     let sArg := substitutePhraseInPhraseHelper phrase arg For depth
                     {node := .app sFn sArg, type := In.type : DPIAPhrase}
    | .depapp fn arg => let sFn := substitutePhraseInPhraseHelper phrase fn For depth
                        {node := .depapp sFn arg, type := In.type : DPIAPhrase}
    | .lam binderName binderType body =>  let sBody := substitutePhraseInPhraseHelper phrase body For (depth+1)
                                          {node := .lam binderName binderType sBody, type := In.type}
    | .deplam binderName binderKind body => let sBody := substitutePhraseInPhraseHelper phrase body For depth
                                            {node := .deplam binderName binderKind sBody, type := In.type : DPIAPhrase}
    | .pair fst snd =>  let sFst := substitutePhraseInPhraseHelper phrase fst For depth
                        let sSnd := substitutePhraseInPhraseHelper phrase snd For depth
                        {node := .pair sFst sSnd, type := In.type : DPIAPhrase}
    | .proj1 p => let sP := substitutePhraseInPhraseHelper phrase p For depth
                  {node := .proj1 sP, type := In.type : DPIAPhrase}
    | .proj2 p => let sP := substitutePhraseInPhraseHelper phrase p For depth
                  {node := .proj1 sP, type := In.type : DPIAPhrase}
    | .ifThenElse cond thenP elseP => let sCond := substitutePhraseInPhraseHelper phrase cond For depth
                                      let sThenP := substitutePhraseInPhraseHelper phrase thenP For depth
                                      let sElseP := substitutePhraseInPhraseHelper phrase elseP For depth
                                      {node := .ifThenElse sCond sThenP sElseP, type := In.type : DPIAPhrase}
--termination_by phraseSize In

def substitutePhraseInPhrase (phrase In : DPIAPhrase) (For : Lean.Name): DPIAPhrase :=
  substitutePhraseInPhraseHelper phrase In For 0

def substituteDWrapper (depArg : DWrapper) (In : PhraseType) (For : Lean.Name) (depth : Nat) : PhraseType:=
  match depArg with
    | .rise (.nat n) => substituteNatInPhraseTypeHelper n For In depth
    | .rise (.data d) => substituteDataInPhraseTypeHelper d For In depth
    | _ => panic! s!"other wrapper types but nat data and readwrite are not implemented yet"

partial def substituteDWrapperInPhraseHelper (depArg : DWrapper) (In : DPIAPhrase) (For : Lean.Name) (depth : Nat): DPIAPhrase :=
  let pt := substituteDWrapper depArg In.type For depth
  match In.node with
    | .bvar _ _ => {node := In.node, type := pt}
    | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => substituteDWrapperInPhraseHelper depArg x For depth) (fun x => x) (fun x => x)), type := pt}
    | .functional func => {node := .functional (substituteInFunctional func (fun x => substituteDWrapperInPhraseHelper depArg x For depth) (fun x => x) (fun x => x)), type := pt}
    | .lit _ => {node := In.node, type := pt}
    | .app fn arg => let sFn := substituteDWrapperInPhraseHelper depArg fn For depth
                     let sArg := substituteDWrapperInPhraseHelper depArg arg For depth
                     {node := .app sFn sArg, type := pt : DPIAPhrase}
    | .depapp fn arg => let sFn := substituteDWrapperInPhraseHelper depArg fn For depth
                        {node := .depapp sFn arg, type := pt : DPIAPhrase}
    | .lam binderName binderType body =>  let sBody := substituteDWrapperInPhraseHelper depArg body For depth
                                          let sBinderType := substituteDWrapper depArg binderType For depth
                                          {node := .lam binderName sBinderType sBody, type := pt}
    | .deplam binderName binderKind body => let sBody := substituteDWrapperInPhraseHelper depArg body For (depth+1)
                                            {node := .deplam binderName binderKind sBody, type := pt : DPIAPhrase}
    | .pair fst snd =>  let sFst := substituteDWrapperInPhraseHelper depArg fst For depth
                        let sSnd := substituteDWrapperInPhraseHelper depArg snd For depth
                        {node := .pair sFst sSnd, type := pt : DPIAPhrase}
    | .proj1 p => let sP := substituteDWrapperInPhraseHelper depArg p For depth
                  {node := .proj1 sP, type := pt : DPIAPhrase}
    | .proj2 p => let sP := substituteDWrapperInPhraseHelper depArg p For depth
                  {node := .proj1 sP, type := pt : DPIAPhrase}
    | .ifThenElse cond thenP elseP => let sCond := substituteDWrapperInPhraseHelper depArg cond For depth
                                      let sThenP := substituteDWrapperInPhraseHelper depArg thenP For depth
                                      let sElseP := substituteDWrapperInPhraseHelper depArg elseP For depth
                                      {node := .ifThenElse sCond sThenP sElseP, type := pt : DPIAPhrase}
--termination_by phraseSize In

def substituteDWrapperInPhrase (depArg : DWrapper) (In : DPIAPhrase) (For : Lean.Name): DPIAPhrase :=
  substituteDWrapperInPhraseHelper depArg In For 0



def phraseTypeSize (pt : PhraseType) : Nat :=
  match pt with
    | .expr _ _ => 1
    | .comm => 1
    | .acc _ => 1
    | .pi _ _ body => 1 + phraseTypeSize body
    | .fn binderType body => 1 +  phraseTypeSize binderType + phraseTypeSize body
    | .phrasePair p1 p2 => 1 + phraseTypeSize p1 + phraseTypeSize p2


def RExprSize (rt : RExpr) : Nat :=
  match rt with
    | ⟨.bvar _ _,_⟩ => 1
    | ⟨.const _,_⟩ => 1
    | ⟨.lit _, _⟩ => 1
    | ⟨.app fn arg,_⟩ => 1 + RExprSize fn + RExprSize arg
    | ⟨.depapp fn _,_⟩ => 1 + RExprSize fn
    | ⟨.lam _ _ body,_⟩ => 1 + RExprSize body
    | ⟨.deplam _ _ body,_⟩ => 1 + RExprSize body
