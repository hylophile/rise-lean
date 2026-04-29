import DPIA.Basic
import Rise.Basic
import DPIA.mkFunctions

------------------- substitute in functional and imperative ---------------------------

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
    | .depIdx ..  => In
    | .idxVec n t idx vec  => .idxVec (natFn n) (dataFn t) (phraseFn idx) (phraseFn vec)
    | .take n m t array => .take (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .drop n m t array => .drop (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .concat n m t nArray mArray => .concat (natFn n) (natFn m) (dataFn t) (phraseFn nArray) (phraseFn mArray)
    | .split n m t a array => .split (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .join n m t a array => .join (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .depJoin .. => In
    | .slide n sz sp t array => .slide (natFn n) (natFn sz) (natFn sp) (dataFn t) (phraseFn array)
    | .circularBuffer n alloc sz s t load array => .circularBuffer (natFn n) (natFn alloc) (natFn sz) (dataFn s) (dataFn t) (phraseFn load) (phraseFn array)
    | .rotateValues n sz t wrt array => .rotateValues (natFn n) (natFn sz) (dataFn t) wrt (phraseFn array)
    | .transpose n m t a array => .transpose (natFn n) (natFn m) (dataFn t) a (phraseFn array)
    | .cycle n m  t array  => .cycle (natFn n) (natFn m) (dataFn t) (phraseFn array)
    | .reorder .. =>  In
    | .transposeDepArray .. =>  In
    | .gather n m t idx array => .gather (natFn n) (natFn m) (dataFn t) (phraseFn idx) (phraseFn array)
    | .scatter n m t idx array => .scatter (natFn n) (natFn m) (dataFn t) (phraseFn idx) (phraseFn array)
    | .padCst n l r t padExpr array => .padCst (natFn n) (natFn l) (natFn r) (dataFn t) (phraseFn padExpr) (phraseFn array)
    | .padClamp n l r t array => .padClamp (natFn n) (natFn l) (natFn r) (dataFn t) (phraseFn array)
    | .padEmpty n r t array => .padEmpty (natFn n) (natFn r) (dataFn t) (phraseFn array)
    | .zip n s t a sArray tArray => .zip (natFn n) (dataFn s) (dataFn t) a (phraseFn sArray) (phraseFn tArray)
    | .unzip n s t a array  => .unzip (natFn n) (dataFn s) (dataFn t) a (phraseFn array)
    | .depZip ..  =>  In
    | .partition .. =>  In
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
    | .depMapSeq .. =>  In
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
    | .reorderAcc      .. => In
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
    | .depIdxAcc .. => In
    | .depJoinAcc .. => In
    | .dMatchI x elemT outT f input => .dMatchI (natFn x) (dataFn elemT) (dataFn outT) (phraseFn f) (phraseFn input)
    | .seq c1 c2 => .seq (phraseFn c1) (phraseFn c2)




----------------- substitute annotations -------------------
-- in DAnnotations
def substituteAnnotationA (a : DAnnotation) (name : Lean.Name) (key : DAnnotation) : DAnnotation :=
  match a with
    | .identifier userName => if userName == name then key else a
    | .read => a
    | .write => a

-- in PhraseTypes
def substituteAnnotationPt (pt : PhraseType) (name : Lean.Name) (key : DAnnotation) : PhraseType :=
  match pt with
    | .expr dt rw => .expr dt (substituteAnnotationA rw name key)
    | .comm => pt
    | .acc _ => pt
    | .pi binderKind userName body => .pi binderKind userName (substituteAnnotationPt body name key)
    | .fn binderType body => .fn (substituteAnnotationPt binderType name key) (substituteAnnotationPt body name key)
    | .phrasePair p1 p2 => .phrasePair (substituteAnnotationPt p1 name key) (substituteAnnotationPt p2 name key)




---------------------- substitute Data ------------------

--in Data
def substituteDataInData (dt : RData) (For : Lean.Name) (In : RData) (depth : Nat): RData :=
  match In with
    | .bvar index userName => if userName.toString == For.toString && depth == index
                              then dt
                              else In
    | .array n aDt => .array n (substituteDataInData dt For aDt depth)
    | .pair p1 p2 => .pair (substituteDataInData dt For p1 depth) (substituteDataInData dt For p2 depth)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => .vector n (substituteDataInData dt For vDt depth)
    | _ => panic! s!"that should never happen"

-- in PhraseTypes
def substituteDataInPtHelper (sN : RData) (For : Lean.Name) (In : PhraseType) (depth : Nat): PhraseType :=
  match In with
    | .expr dt rw => .expr (substituteDataInData sN For dt depth) rw
    | .comm => In
    | .acc dt => .acc (substituteDataInData sN For dt depth)
    | .pi binderKind userName body => .pi binderKind userName (substituteDataInPtHelper sN For body (depth +1))
    | .fn binderType body => .fn (substituteDataInPtHelper sN For binderType depth)
                                 (substituteDataInPtHelper sN For body depth)
    | .phrasePair p1 p2 => .phrasePair (substituteDataInPtHelper sN For p1 depth)
                                       (substituteDataInPtHelper sN For p2 depth)

def substituteDataInPhraseType (sN : RData) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  substituteDataInPtHelper sN For In 0


-------------------------- substitute Nat ------------------------

-- in Data
def substituteNatInData (n : RNat) (For : Lean.Name) (In : RData) (depth : Nat): RData :=
  match In with
    | .bvar index userName => if userName.toString == For.toString && depth == index then .natType else In
    | .array n aDt => .array n (substituteNatInData n For aDt depth)
    | .pair p1 p2 => .pair (substituteNatInData n For p1 depth) (substituteNatInData n For p2 depth)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => .vector n (substituteNatInData n For vDt depth)
    | _ => panic! s!"that should never happen"

-- in Nat
partial def substituteNatInNat (num: RNat) (For : Lean.Name) (In: RNat) (depth : Nat) : RNat :=
  match In with
    | .bvar idx name => if name.toString == For.toString && depth == idx then num else In
    | .nat _ => In
    | .plus n m => .plus (substituteNatInNat n For In depth) (substituteNatInNat m For In depth)
    | .minus n m => .minus (substituteNatInNat n For In depth) (substituteNatInNat m For In depth)
    | .mult n m => .mult (substituteNatInNat n For In depth) (substituteNatInNat m For In depth)
    | .div n m => .div (substituteNatInNat n For In depth) (substituteNatInNat m For In depth)
    | .pow n m => .pow (substituteNatInNat n For In depth) (substituteNatInNat m For In depth)
    | _ => panic! s!"there should not be any mvars anymore"

-- in PhraseTypes
def substituteNatInPtHelper (sN : RNat) (For : Lean.Name) (In : PhraseType) (depth : Nat) : PhraseType :=
  match In with
    | .expr dt rw => .expr (substituteNatInData sN For dt depth) rw
    | .comm => In
    | .acc dt => .acc (substituteNatInData sN For dt depth)
    | .pi binderKind userName body => .pi binderKind userName (substituteNatInPtHelper sN For body (depth +1))
    | .fn binderType body => .fn (substituteNatInPtHelper sN For binderType depth)
                                 (substituteNatInPtHelper sN For body depth)
    | .phrasePair p1 p2 => .phrasePair (substituteNatInPtHelper sN For p1 depth)
                                       (substituteNatInPtHelper sN For p2 depth)

def substituteNatInPhraseType (sN : RNat) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  substituteNatInPtHelper sN For In 0
