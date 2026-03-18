import DPIA.Basic
import Rise.Basic

-- hopefully I will be able to reuse it
def substituteInFunctional (In : FunctionalPrimitives) (fn : DPIAPhrase → DPIAPhrase) : FunctionalPrimitives :=
  match In with
    | .id val => .id (fn val)
    | .neg val => .neg (fn val)
    | .add lhs rhs => .add (fn lhs) (fn rhs)
    | .sub lhs rhs => .sub (fn lhs) (fn rhs)
    | .mul lhs rhs => .mul (fn lhs) (fn rhs)
    | .div lhs rhs => .div  (fn lhs) (fn rhs)
    | .mod lhs rhs => .mod (fn lhs) (fn rhs)
    | .not val => .not (fn val)
    | .gt lhs rhs => .gt (fn lhs) (fn rhs)
    | .lt lhs rhs => .lt (fn lhs) (fn rhs)
    | .equal lhs rhs => .equal (fn lhs) (fn rhs)
    | .cast s t x => .cast s t (fn x)
    | .indexAsNat n idx => .indexAsNat n (fn idx)
    | .natAsIndex n idx => .natAsIndex n (fn idx)
    | .rlet s t a f val => .rlet s t a (fn f) (fn val)
    | .toMem t input => .toMem t (fn input)
    | .generate n t f  => .generate n t (fn f)
    | .idx n t idx array => .idx n t (fn idx) (fn array)
    | .depIdx ..  => In -- needs to be fixed at some point
    | .idxVec n t idx vec  => .idxVec n t (fn idx) (fn vec)
    | .take n m t array => .take n m t (fn array)
    | .drop n m t array => .drop n m t (fn array)
    | .concat n m t nArray mArray => .concat n m t (fn nArray) (fn mArray)
    | .split n m t a array => .split n m t a (fn array)
    | .join n m t a array => .join n m t a (fn array)
    | .depJoin .. => In  -- needs to be fixed at some point
    | .slide n sz sp t array => .slide n sz sp t (fn array)
    | .circularBuffer n alloc sz s t load array => .circularBuffer n alloc sz s t (fn load) (fn array)
    | .rotateValues n sz t wrt array => .rotateValues n sz t wrt (fn array)
    | .transpose n m t a array => .transpose n m t a (fn array)
    | .cycle n m  t array  => .cycle n m t (fn array)
    | .reorder .. =>  In  -- needs to be fixed at some point
    | .transposeDepArray .. =>  In  -- needs to be fixed at some point
    | .gather n m t idx array => .gather n m t (fn idx) (fn array)
    | .scatter n m t idx array => .scatter n m t (fn idx) (fn array)
    | .padCst n l r t padExpr array => .padCst n l r t (fn padExpr) (fn array)
    | .padClamp n l r t array => .padClamp n l r t (fn array)
    | .padEmpty n r t array => .padEmpty n r t (fn array)
    | .zip n s t a sArray tArray => .zip n s t a (fn sArray) (fn tArray)
    | .unzip n s t a array  => .unzip n s t a (fn array)
    | .depZip ..  =>  In  -- needs to be fixed at some point
    | .partition .. =>  In  -- needs to be fixed at some point
    | .makePair s t a fst snd  => .makePair s t a (fn fst) (fn snd)
    | .fst s t pair => .fst s t (fn pair)
    | .snd s t pair => .snd s t (fn pair)
    | .vectorFromScalar n t arg  => .vectorFromScalar n t (fn arg)
    | .asVector n m t a array  => .asVector n m t a (fn array)
    | .asVectorAligned n m t a array  => .asVectorAligned n m t a (fn array)
    | .asScalar n m t a array => .asScalar n m t a (fn array)
    | .map n s t a f array => .map n s t a (fn f) (fn array)
    | .mapSeq unroll n s t f array => .mapSeq unroll n s t (fn f) (fn array)
    | .mapStream n s t f array  => .mapStream n s t (fn f) (fn array)
    | .iterateStream n s t f array => .iterateStream n s t (fn f) (fn array)
    | .depMapSeq .. =>  In  -- needs to be fixed at some point
    | .mapVec n t1 t2 f vec  => .mapVec n t1 t2 (fn f) (fn vec)
    | .mapFst s1 t s2 a f pair => .mapFst s1 t s2 a (fn f) (fn pair)
    | .mapSnd s t1 t2 a f pair => .mapSnd s t1 t2 a (fn f) (fn pair)
    | .reduceSeq unroll n  s t f init array  => .reduceSeq unroll n s t (fn f) (fn init) (fn array)
    | .scanSeq n s t f init array => .scanSeq n s t (fn f) (fn init) (fn array)
    | .iterate n m k t f array => .iterate n m k t (fn f) (fn array)
    | .depTile n tileSize haloSize t1 t2 processTiles array  => .depTile n tileSize haloSize t1 t2 (fn processTiles) (fn array)
    | .printType msg t a input  => .printType msg t a (fn input)


-- hopefully I will be able to reuse it
def substituteInImperative (In : ImperativePrimitives) (fn : DPIAPhrase → DPIAPhrase) : ImperativePrimitives :=
  match In with
    | .asScalarAcc n m t array => .asScalarAcc n m t (fn array)
    | .assign t lhs rhs => .assign t (fn lhs) (fn rhs)
    | .asVectorAcc n m t array => .asVectorAcc n m t (fn array)
    | .forLoop unroll n body  => .forLoop unroll n (fn body)
    | .forNat unroll n body => .forNat unroll n (fn body)
    | .forVec n t out body => .forVec n t (fn out) (fn body)
    | .generateCont n t f  => .generateCont n t (fn f)
    | .idxAcc n t idx array => .idxAcc n t (fn idx) (fn array)
    | .idxVecAcc n t idx vec => .idxVecAcc n t (fn idx) (fn vec)
    | .scatterAcc n m t indicies array => .scatterAcc n m t (fn indicies) (fn array)
    | .splitAcc n m t array => .splitAcc n m t (fn array)
    | .joinAcc n m t array => .joinAcc n m t (fn array)
    | .unzipAcc n t1 t2 array => .unzipAcc n t1 t2 (fn array)
    | .zipAcc1     n t1 t2 array => .zipAcc1 n t1 t2 (fn array)
    | .zipAcc2     n t1 t2 array => .zipAcc2 n t1 t2 (fn array)
    | .transposeAcc n m t array  => .transposeAcc n m t (fn array)
    | .cycleAcc n m t input => .cycleAcc n m t (fn input)
    | .reorderAcc      .. => In  -- needs to be fixed at some point
    | .dropAcc n m t array => .dropAcc n m t (fn array)
    | .takeAcc n m t array => .takeAcc n m t (fn array)
    | .mapAcc n t1 t2 t3 f array => .mapAcc n t1 t2 t3 (fn f) (fn array)
    | .mapFstAcc t1 t2 t3 f record  => .mapFstAcc t1 t2 t3 (fn f) (fn record)
    | .mapRead n t1 t2 t3 f input => .mapRead n t1 t2 t3 (fn f) (fn input)
    | .mapSndAcc t1 t2 t3 f record => .mapSndAcc t1 t2 t3 (fn f) (fn record)
    | .mkDPairFstl fst a => .mkDPairFstl fst (fn a)
    | .mkDPairSndAcc fst sndT a => .mkDPairSndAcc fst sndT (fn a)
    | .pairAcc t1 t2 fst snd => .pairAcc t1 t2 (fn fst)  (fn snd)
    | .pairAcc1 t1 t2 pair => .pairAcc1 t1 t2 (fn pair)
    | .pairAcc2 t1 t2 pair => .pairAcc2 t1 t2 (fn pair)
    | .new t f => .new t (fn f)
    | .newDoubleBuffer n t1 t2 t3 input out f => .newDoubleBuffer n t1 t2 t3 (fn input) (fn out) (fn f)
    | .comment _ => In
    | .skip => In
    | .depIdxAcc .. => In  -- needs to be fixed at some point
    | .depJoinAcc .. => In  -- needs to be fixed at some point
    | .dMatchI x elemT outT f input => .dMatchI x elemT outT (fn f) (fn input)
    | .seq c1 c2 => .seq (fn c1) (fn c2)

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
    | .bvar index userName => dbg_trace s!"for is {For} with depth {depth} and name is {userName} with index {index}"
                              if userName.toString == For.toString && depth == index
                              then dbg_trace s!"i chose true and return {dt}"
                                   dt
                              else dbg_trace s!"i chose false"
                                   In --> not sure how to include deBruijnIndex yet --> need to take a look at it again
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
    | .bvar deBruijnIndex userName => if userName == For && deBruijnIndex == depth && In.type == phrase.type then phrase
                                      else In
    | .imperative imp => {node := .imperative (substituteInImperative imp (fun x => substitutePhraseInPhraseHelper phrase x For depth)), type := In.type}
    | .functional func => {node := .functional (substituteInFunctional func (fun x => substitutePhraseInPhraseHelper phrase x For depth)), type := In.type}
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

partial def substituteNatInRExprPtHelper (nat : RNat) (In : RExprPt) (For : Lean.Name) (depth : Nat): RExprPt :=
  let type := substituteNatInPhraseType nat For In.type
  let node := match In.node with
              | .app fn arg => .app (substituteNatInRExprPtHelper nat fn For depth) (substituteNatInRExprPtHelper nat arg For depth)
              | .depapp fn arg => .depapp (substituteNatInRExprPtHelper nat fn For depth) arg
              | .lam binderName binderType body => .lam binderName
                                                        (substituteNatInRType nat For binderType depth)
                                                        (substituteNatInRExprPtHelper nat body For depth)
              | .deplam binderName binderKind body => .deplam   binderName
                                                                binderKind
                                                                (substituteNatInRExprPtHelper nat body For (depth+1))
              | _ => In.node
  {node := node, type:=type}

partial def substituteDataInRExprPtHelper (data : RData) (In : RExprPt) (For : Lean.Name) (depth : Nat): RExprPt :=
  let type := substituteDataInPhraseType data For In.type
  let node := match In.node with
              | .app fn arg => .app (substituteDataInRExprPtHelper data fn For depth) (substituteDataInRExprPtHelper data arg For depth)
              | .depapp fn arg => .depapp (substituteDataInRExprPtHelper data fn For depth) arg
              | .lam binderName binderType body => .lam binderName
                                                        (substituteDataInRType data For binderType depth)
                                                        (substituteDataInRExprPtHelper data body For depth)
              | .deplam binderName binderKind body => .deplam   binderName
                                                                binderKind
                                                                (substituteDataInRExprPtHelper data body For (depth+1))
              | _ => In.node
  {node := node, type:=type}

-- def matchTypeDependentOnKind (k : DKind) : Type :=
--   match k with
--     | .rise r => match r with
--                   | .data => RData
--                   | .nat => RNat
--                   | _ => panic! s!"cannot return a Type"
--     | .readWrite => DAnnotation
--     | _ => panic! s!"cannot return a Type"


-- substitute kinds in PhraseTypes
-- def substituteKindsPt {T : Type} (binderKind : DKind) (x : matchTypeDependentOnKind binderKind) (For : Lean.Name) (In : PhraseType) : PhraseType :=
--   match binderKind, x with
--     | DKind.rise RKind.data , (x : RData) => substituteDataPt x For In
--     | DKind.rise RKind.nat , (x : RNat) => substituteNatPt x For In
--     | DKind.readWrite, (x : DAnnotation) => substituteAnnotationPt In For x
--     | _, _ => panic! s!"could not substitute x in {For}"

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
