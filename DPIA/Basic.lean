import Rise.Basic

-- NatToNat
inductive NatToNat where
  | natToNatIdentifier (userName : Lean.Name)
  | natToNatLambda (x : Nat) (body : RNat)
deriving BEq, Repr

inductive NatToData where
  | natToDataIdentifier (userName : Lean.Name)
  | natToDataLambda (x : Nat) (body : RData)
deriving BEq, Repr


-- Kind
--   κ ::= nat | data |  (Natural Number Kind, Datatype Kind) | readWrite
-- all rise RKinds and readWrite
inductive DKind
  | rise (k: RKind)
  | readWrite
  | natToNat --(n : NatToNat)
  | natToData --(n : NatToData)
deriving BEq, Repr


inductive DAnnotation
  | identifier (userName: Lean.Name) -- for now only a identifier
  | read
  | write
deriving Repr, BEq

-- Types
--   τ ::= τ → τ | (x : κ) → τ (Data Type, Function Type, Dependent Function Type)
--         τ x τ | exp[dt , rw] | acc[ dt ] | Comm
inductive PhraseType
  | expr (dt : RData) (rw : DAnnotation)
  | comm
  | acc (dt : RData)
  | pi (binderKind : DKind) (userName : Lean.Name) (body : PhraseType)
  | fn (binderType : PhraseType) (body : PhraseType)
  | phrasePair (p1 : PhraseType) (p2 : PhraseType)
deriving Repr, BEq

-- all rise RWrappers plus readWrite
inductive DWrapper
  | rise (w: RWrapper)
  | readWrite (v: DAnnotation)
deriving Repr, BEq

abbrev RExprPt := RExprWith PhraseType
abbrev RExprNodePt := RExprNodeWith PhraseType

mutual
structure DPIAPhrase where
  node: DPIAPhraseNode
  type: PhraseType
deriving Repr, BEq

inductive DPIAPhraseNode where
  | bvar (deBruijnIndex : Nat) (userName: Lean.Name)
  | imperative (imp : ImperativePrimitives)
  | functional (prim : FunctionalPrimitives)
  | lit (val : RLit)
  | app (fn arg : DPIAPhrase)
  | depapp (fn : DPIAPhrase) (arg : DWrapper)
  | lam (binderName : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase)
  | deplam (binderName : Lean.Name) (binderKind : DKind) (body : DPIAPhrase)
  | pair (fst snd: DPIAPhrase)
  | proj1 (p: DPIAPhrase)
  | proj2 (p: DPIAPhrase)
  | ifThenElse (cond thenP elseP: DPIAPhrase)
deriving Repr, BEq


--------- Functional primitives ---------------------

inductive FunctionalPrimitives where
  -- unary ops
  | id      (t : DPIAPhrase)
  | neg     (t : DPIAPhrase)

  -- binary ops
  | add     (lhs rhs : DPIAPhrase)
  | sub     (lhs rhs : DPIAPhrase)
  | mul     (lhs rhs : DPIAPhrase)
  | div     (lhs rhs : DPIAPhrase)
  | mod     (lhs rhs : DPIAPhrase)

  -- ternary ops
  --| select  (t : RData) (cond : RData) -- TODO select : {t : data} → bool → t → t → t

  -- comparison ops
  | not     (v : DPIAPhrase)
  | gt      (lhs rhs : DPIAPhrase)
  | lt      (lhs rhs : DPIAPhrase)
  | equal   (lhs rhs : DPIAPhrase)

  -- cast ops
  | cast          (s t : RData) (x : DPIAPhrase)
  | indexAsNat    (n : RNat) (idx : DPIAPhrase)
  | natAsIndex    (n : RNat) (idx : DPIAPhrase)

  -- memory ops
  | rlet    (s t : RData) (a : DAnnotation) (f val: DPIAPhrase)
  | toMem   (t : RData) (input : DPIAPhrase)

  -- array ops
  | generate    (n : RNat) (t : RData) (f : DPIAPhrase)
  | idx         (n : RNat) (t : RData) (idx array : DPIAPhrase)

  | depIdx      (n idx: RNat) (ft : NatToData) (array : DPIAPhrase)
  | idxVec      (n : RNat) (t : RData) (idx vec : DPIAPhrase)

  | take      (n m : RNat) (t : RData) (array : DPIAPhrase)
  | drop      (n m : RNat) (t : RData) (array : DPIAPhrase)
  | concat    (n m : RNat) (t : RData) (nArray mArray : DPIAPhrase)

  | split     (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | join      (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | depJoin   (n : RNat) (lenF : NatToData) (t : RData) (array : DPIAPhrase)

  | slide               (n sz sp : RNat) (t : RData) (array : DPIAPhrase)
  | circularBuffer      (n alloc sz : RNat) (s t : RData) (load array : DPIAPhrase)
  | rotateValues        (n sz : RNat) (t : RData) (wrt array : DPIAPhrase)

  | transpose           (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | cycle               (n m : RNat) (t : RData) (array : DPIAPhrase)
  | reorder             (n : RNat) (idxF : NatToNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | transposeDepArray   (n m : RNat) (ft : NatToData) (array : DPIAPhrase)

  | gather      (n m : RNat) (t : RData) (idx array : DPIAPhrase)
  | scatter     (n m : RNat) (t : RData) (idx array : DPIAPhrase)

  | padCst      (n l r : RNat) (t : RData) (padExpr array : DPIAPhrase)
  | padClamp    (n l r : RNat) (t : RData) (array : DPIAPhrase)
  | padEmpty    (n r : RNat) (t : RData) (array : DPIAPhrase)

  | zip       (n : RNat) (s t : RData) (a : DAnnotation) (sArray tArray : DPIAPhrase)
  | unzip     (n : RNat) (s t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | depZip    (n : RNat) (ft1 ft2 : NatToData)(e1 e2 : DPIAPhrase)

  -- | makeArray   (n : RNat) (t : RData) (elements : List DPIAPhrase) --- TODO (n : Int)

  | partition   (n m : RNat) (lenF : NatToNat) (t : RData) (array : DPIAPhrase)

  -- pair ops
  | makePair      (s t : RData) (a : DAnnotation) (fst snd : DPIAPhrase)
  -- | makeDepPair   (fst : RNat) (sndT : RData) (a : DAnnotation) (snd : DPIAPhrase)  -- TODO (fst : NatIdentifier)
  | fst           (s t : RData) (pair : DPIAPhrase)
  | snd           (s t : RData) (pair : DPIAPhrase)

  -- vector ops
  | vectorFromScalar    (n : RNat) (t : RData) (arg : DPIAPhrase)
  | asVector            (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | asVectorAligned     (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | asScalar            (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)

  -- map
  | map               (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase)
  | mapSeq            (unroll : Bool) (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | mapStream         (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | iterateStream     (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | depMapSeq         (unroll : Bool) (n : RNat) (ft1 ft2 : NatToData) (f array: DPIAPhrase)
  | mapVec            (n : RNat) (t1 t2 : RData) (f vec : DPIAPhrase)

  | mapFst    (s1 t s2 : RData) (a : DAnnotation) (f pair : DPIAPhrase)
  | mapSnd    (s t1 t2 : RData) (a : DAnnotation) (f pair : DPIAPhrase)

  -- reduce
  | reduceSeq (unroll : Bool) (n : RNat) (s t : RData) (f init array : DPIAPhrase)

  -- scan
  | scanSeq (n :RNat) (s t : RData) (f init array : DPIAPhrase)

  -- iterate
  | iterate (n m k : RNat) (t : RData) (f array : DPIAPhrase)

  -- ? TODO
  | depTile       (n tileSize haloSize : RNat) (t1 t2 : RData) (processTiles array : DPIAPhrase)
  -- | dMatch        (x : RNat) (elemT outT : RData) (a : DAnnotation) (f array : DPIAPhrase) -- TODO (x : NatIdentifier)
  | printType     (msg : String) (t : RData) (a : DAnnotation) (input : DPIAPhrase)
deriving Repr, BEq

------------- imperial primitives --------------------------

inductive ImperativePrimitives where

  -- vector ops
  | asScalarAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)
  | assign          (t : RData) (lhs rhs : DPIAPhrase)
  | asVectorAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  -- for ops
  | forLoop     (unroll : Bool) (n : RNat) (body : DPIAPhrase)-- for not possible as key -> unroll?
  | forNat      (unroll : Bool) (n : RNat) (body : DPIAPhrase)
  | forVec      (n : RNat) (t : RData) (out body : DPIAPhrase)

  -- array ops
  | generateCont    (n : RNat) (t : RData) (f : DPIAPhrase)
  | idxAcc          (n : RNat) (t : RData) (idx array: DPIAPhrase)
  | idxVecAcc       (n : RNat) (t : RData) (idx vec : DPIAPhrase)

  | scatterAcc      (n m : RNat) (t : RData) (indicies array : DPIAPhrase)

  | splitAcc    (n m : RNat) (t : RData) (array : DPIAPhrase)
  | joinAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  | unzipAcc    (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)
  | zipAcc1     (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)
  | zipAcc2     (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)

  | transposeAcc    (n m : RNat) (t : RData) (array : DPIAPhrase)
  | cycleAcc        (n m : RNat) (t : RData) (input : DPIAPhrase)
  | reorderAcc      (n : RNat) (idxF : NatToNat) (t : RData) (array : DPIAPhrase)

  | dropAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)
  | takeAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  -- map ops
  | mapAcc        (n : RNat) (t1 t2 : RData) (f array : DPIAPhrase)
  | mapFstAcc     (t1 t2 t3 : RData) (f record : DPIAPhrase)
  | mapRead       (n : RNat) (t1 t2 : RData) (f input : DPIAPhrase)
  | mapSndAcc     (t1 t2 t3 : RData) (f record : DPIAPhrase)

  -- pair ops
  | mkDPairFstl       (fst : RNat) (a : DPIAPhrase)
  | mkDPairSndAcc     (fst : RNat) (sndT : RData) (a : DPIAPhrase) --TODO: what does it do?

  | pairAcc     (t1 t2 : RData) (fst snd : DPIAPhrase)
  | pairAcc1    (t1 t2 : RData) (pair : DPIAPhrase)
  | pairAcc2    (t1 t2 : RData) (pair : DPIAPhrase)

  -- memory ops
  | new                 (t : RData) (f : DPIAPhrase)
  | newDoubleBuffer     (n : RNat) (t1 t2 t3 : RData) (input out f : DPIAPhrase)

  | comment   (comment : String)
  | skip

  -- ? TODO
  | depIdxAcc     (n idx : RNat) (ft : NatToData) (array : DPIAPhrase)
  | depJoinAcc    (n : RNat) (lenF : NatToNat) (t : RData) (array : DPIAPhrase)
  | dMatchI       (x : RNat) (elemT outT : RData) (f input : DPIAPhrase) -- NatIdentifier? (x : natIdentifier)
  | seq           (c1 c2 : DPIAPhrase)

deriving Repr, BEq

end

------------ inhabited ------------------------- for throwing errors
instance : Inhabited DPIAPhrase :=
  ⟨{node := DPIAPhraseNode.bvar 0 (Lean.Name.mkSimple "dummy"), type := PhraseType.comm : DPIAPhrase}⟩

instance : Inhabited DPIAPhraseNode :=
  ⟨DPIAPhraseNode.bvar 0 (Lean.Name.mkSimple "dummy")⟩

instance : Inhabited PhraseType :=
  ⟨PhraseType.comm⟩

instance : Inhabited RData :=
  ⟨RData.natType⟩

instance : Inhabited RNat :=
  ⟨RNat.nat 0⟩

instance : Inhabited DAnnotation :=
  ⟨DAnnotation.read⟩

instance : Inhabited RType :=
  ⟨RType.data RData.natType⟩

instance : Inhabited (RExprWith PhraseType) :=
  ⟨{node := .lit (.bool false), type := PhraseType.comm : RExprPt}⟩

------------ Representations ----------------------

-- modified from Nate
instance : ToString DKind where
  toString
    | DKind.rise k => s!"{k}"
    | DKind.readWrite => "rw"
    | DKind.natToData => "nat→data"
    | DKind.natToNat => "nat→nat"


instance : ToString DAnnotation where
  toString
    | .identifier name => s!"{name}"
    | .read => "rd"
    | .write => "wr"

def NatToNat.apply (nat2nat : NatToNat) (n : RNat) : RNat :=
  match nat2nat with
    | NatToNat.natToNatIdentifier userName => RNat.bvar 0 userName --?
    | NatToNat.natToNatLambda x body => RNat.substNat body x n

def NatToData.apply (nat2nat : NatToData) (n : RNat) : RData :=
  match nat2nat with
    | NatToData.natToDataIdentifier userName => RData.bvar 0 userName --?
    | NatToData.natToDataLambda x body => RData.substNat body x n

def assertDataType (exprT: RType) : RData :=
  match exprT with
    | .data dt => dt
    | _ => panic! s!"THis should never happen"

def assertFunctionType (exprT: RType) : RType :=
  match exprT with
    | .fn inT _ => inT
    | _ => panic! s!"THis should never happen"

def assertFunctionTypePt (exprT: PhraseType) : PhraseType :=
  match exprT with
    | .fn _ _ => exprT
    | _ => panic! s!"THis should never happen"


-- modified from Nate
def PhraseType.toString : PhraseType → String
  | PhraseType.expr dt rw => s!"expr[{RData.toString dt} | {rw}]"
  | PhraseType.comm => s!"comm"
  | PhraseType.acc dt => s!" acc [{RData.toString dt}]"
  | PhraseType.pi kind un body =>
      s!"({un} : {kind}) → {PhraseType.toString body}"
  | PhraseType.fn binderType body =>
    match binderType with
    | .fn .. | .pi .. => s!"({PhraseType.toString binderType}) → {PhraseType.toString body}"
    | _ => s!"{PhraseType.toString binderType} → {PhraseType.toString body}"
  | PhraseType.phrasePair p1 p2 => s!"{PhraseType.toString p1} x {PhraseType.toString p2}"

-- modified from Nate
instance : ToString PhraseType where
  toString := PhraseType.toString

-- modified from Nate
def DWrapper.render : DWrapper -> Std.Format
  | .rise w => w.render
  | .readWrite v => toString v ++ " : readWrite"

def setNestAndLine (indent : Int) (f : Std.Format) : Std.Format :=
  Std.Format.nest indent (Std.Format.line ++ f)

mutual
partial def FunctionalPrimitives.render : FunctionalPrimitives → Std.Format
  | .id val => s!"id {val.node.render}"
  | .neg val => s!"neg {val.node.render}"
  | .add lhs rhs => "add " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .sub lhs rhs => "sub " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .mul lhs rhs => "mul " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .div lhs rhs => "div " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .mod lhs rhs => "mod " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .not val => s!"not" ++ setNestAndLine 2 val.node.render
  | .gt lhs rhs => "gt " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .lt lhs rhs => "lt " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .equal lhs rhs => "equal " ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .cast s t x => s!"cast {s} {t}" ++ setNestAndLine 2 x.node.render
  | .indexAsNat n idx => s!"indexAsNat {n}" ++ setNestAndLine 2 idx.node.render
  | .natAsIndex n idx => s!"natAsIndex {n}" ++ setNestAndLine 2 idx.node.render
  | .rlet s t a f val => s!"rlet {s} {t} {a}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 val.node.render
  | .toMem t input => s!"toMem {t}" ++ setNestAndLine 2 input.node.render
  | .generate n t f  => s!"generate {n} {t}" ++ setNestAndLine 2 f.node.render
  | .idx n t idx array => s!"idx {n} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 array.node.render
  | .depIdx ..  => s!"string for functional depIdx is not defined yet"
  | .idxVec n t idx vec  => s!"idxVec {n} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 vec.node.render
  | .take n m t array => s!"take {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .drop n m t array => s!"drop {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .concat n m t nArray mArray => s!"concat {n} {m} {t}" ++ setNestAndLine 2 nArray.node.render ++ setNestAndLine 2 mArray.node.render
  | .split n m t a array => s!"split {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .join n m t a array => s!"join {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .depJoin .. => s!"string for functional depJoin is not defined yet"
  | .slide n sz sp t array => s!"slide {n} {sz} {sp} {t}" ++ setNestAndLine 2 array.node.render
  | .circularBuffer n alloc sz s t load array => s!"circularBuffer {n} {alloc} {sz} {s} {t}" ++ setNestAndLine 2 load.node.render ++ setNestAndLine 2 array.node.render
  | .rotateValues n sz t wrt array => s!"rotateValues {n} {sz} {t}" ++ setNestAndLine 2 wrt.node.render ++ setNestAndLine 2 array.node.render
  | .transpose n m t a array => s!"transpose {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .cycle n m  t array  => s!"cycle {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .reorder .. => s!"string for functional reorder is not defined yet"
  | .transposeDepArray .. => s!"string for functional transposeDepArray is not defined yet"
  | .gather n m t idx array => s!"gather {n} {m} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 array.node.render
  | .scatter n m t idx array => s!"scatter {n} {m} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 array.node.render
  | .padCst n l r t padExpr array => s!"padCst {n} {l} {r} {t}" ++ setNestAndLine 2 padExpr.node.render ++ setNestAndLine 2 array.node.render
  | .padClamp n l r t array => s!"padClamp {n} {l} {r} {t}" ++ setNestAndLine 2 array.node.render
  | .padEmpty n r t array => s!"padEmpty {n} {r} {t}" ++ setNestAndLine 2 array.node.render
  | .zip n s t a sArray tArray => s!"zip {n} {s} {t} {a}" ++ setNestAndLine 2 sArray.node.render ++ setNestAndLine 2 tArray.node.render
  | .unzip n s t a array  => s!"unzip {n} {s} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .depZip ..  => s!"string for functional depZip is not defined yet"
  | .partition .. => s!"string for functional partition is not defined yet"
  | .makePair s t a fst snd  => s!"makePair {s} {t} {a}" ++ setNestAndLine 2 fst.node.render ++ setNestAndLine 2 snd.node.render
  | .fst s t pair => s!"fst {s} {t}" ++ setNestAndLine 2 pair.node.render
  | .snd s t pair => s!"snd {s} {t}" ++ setNestAndLine 2 pair.node.render
  | .vectorFromScalar n t arg  => s!"vectorFromScalar {n} {t}" ++ setNestAndLine 2 arg.node.render
  | .asVector n m t a array  => s!"asVector {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .asVectorAligned n m t a array  => s!"asVectorAligned {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .asScalar n m t a array => s!"asScalar {n} {m} {t} {a}" ++ setNestAndLine 2 array.node.render
  | .map n s t a f array => s!"map {n} {s} {t} {a}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .mapSeq unroll n s t f array => s!"mapSeq {unroll} {n} {s} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .mapStream n s t f array  => s!"mapStream {n} {s} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .iterateStream n s t f array => s!"iterateStream {n} {s} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .depMapSeq .. => s!"string for functional depMapSeq is not defined yet"
  | .mapVec n t1 t2 f vec  => s!"mapVec {n} {t1} {t2}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 vec.node.render
  | .mapFst s1 t s2 a f pair => s!"mapFst {s1} {t} {s2} {a}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 pair.node.render
  | .mapSnd s t1 t2 a f pair => s!"mapSnd {s} {t1} {t2} {a}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 pair.node.render
  | .reduceSeq unroll n  s t f init array  => s!"reduceSeq {unroll} {n} {s} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 init.node.render ++ setNestAndLine 2 array.node.render
  | .scanSeq n s t f init array => s!"scanSeq {n} {s} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 init.node.render ++ setNestAndLine 2 array.node.render
  | .iterate n m k t f array => s!"iterate {n} {m} {k} {t}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .depTile n tileSize haloSize t1 t2 processTiles array  => s!"depTile {n} {tileSize} {haloSize} {t1} {t2}" ++ setNestAndLine 2 processTiles.node.render ++ setNestAndLine 2 array.node.render
  | .printType msg t a input  => s!"printType {msg} {t} {a}" ++ setNestAndLine 2 input.node.render

partial def ImperativePrimitives.render : ImperativePrimitives → Std.Format
  | .asScalarAcc n m t array => s!"asScalarAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .assign t lhs rhs => s!"assign {t}" ++ setNestAndLine 2 lhs.node.render ++ setNestAndLine 2 rhs.node.render
  | .asVectorAcc n m t array => s!"asvectorAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .forLoop unroll n body  => s!"for {unroll} {n}" ++ setNestAndLine 2 body.node.render
  | .forNat unroll n body => s!"forNat {unroll} {n}" ++ setNestAndLine 2 body.node.render
  | .forVec n t out body => s!"forVec {n} {t}" ++ setNestAndLine 2 out.node.render ++ setNestAndLine 2 body.node.render
  | .generateCont n t f  => s!"generateCont {n} {t}" ++ setNestAndLine 2 f.node.render
  | .idxAcc n t idx array => s!"idxAcc {n} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 array.node.render
  | .idxVecAcc n t idx vec => s!"idxVexAcc {n} {t}" ++ setNestAndLine 2 idx.node.render ++ setNestAndLine 2 vec.node.render
  | .scatterAcc n m t indicies array => s!"scatterAcc {n} {m} {t}" ++ setNestAndLine 2 indicies.node.render ++ setNestAndLine 2  array.node.render
  | .splitAcc n m t array => s!"splitAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .joinAcc n m t array => s!"joinAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .unzipAcc n t1 t2 array => s!"unzip {n} {t1} {t2}" ++ setNestAndLine 2 array.node.render
  | .zipAcc1     n t1 t2 array => s!"zipAcc1 {n} {t1} {t2}" ++ setNestAndLine 2 array.node.render
  | .zipAcc2     n t1 t2 array => s!"zipAcc2 {n} {t1} {t2}" ++ setNestAndLine 2 array.node.render
  | .transposeAcc n m t array  => s!"transposeAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .cycleAcc n m t input => s!"cycleAcc {n} {m} {t}" ++ setNestAndLine 2 input.node.render
  | .reorderAcc      .. => s!"string for imperative reorderAcc is not defined yet"
  | .dropAcc n m t array => s!"dropAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .takeAcc n m t array => s!"takeAcc {n} {m} {t}" ++ setNestAndLine 2 array.node.render
  | .mapAcc n t1 t2 f array => s!"mapAcc {n} {t1} {t2}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 array.node.render
  | .mapFstAcc t1 t2 t3 f record  => s!"mapFstAcc {t1} {t2} {t3}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 record.node.render
  | .mapRead n t1 t2 f input => s!"mapRead {n} {t1} {t2}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 input.node.render
  | .mapSndAcc t1 t2 t3 f record => s!"mapSndAcc {t1} {t2} {t3}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 record.node.render
  | .mkDPairFstl fst a => s!"mkDPairFstl {fst}" ++ setNestAndLine 2 a.node.render
  | .mkDPairSndAcc fst sndT a => s!"mkDPairSndAcc {fst} {sndT}" ++ setNestAndLine 2 a.node.render
  | .pairAcc t1 t2 fst snd => s!"pairAcc {t1} {t2}" ++ setNestAndLine 2 fst.node.render ++ setNestAndLine 2 snd.node.render
  | .pairAcc1 t1 t2 pair => s!"pairAcc1 {t1} {t2}" ++ setNestAndLine 2 pair.node.render
  | .pairAcc2 t1 t2 pair => s!"pairAcc2 {t1} {t2}" ++ setNestAndLine 2 pair.node.render
  | .new t f => s!"new {t}" ++ setNestAndLine 2 f.node.render
  | .newDoubleBuffer n t1 t2 t3 input out f => s!"newDoubleBuffer {n} {t1} {t2} {t3}" ++ setNestAndLine 2 input.node.render ++ setNestAndLine 2 out.node.render ++ setNestAndLine 2 f.node.render
  | .comment comment => s!"comment -- {comment} --"
  | .skip => s!"skip"
  | .depIdxAcc .. => s!"string for imperative depIdxAcc is not defined yet"
  | .depJoinAcc .. => s!"string for imperative depIdxAcc is not defined yet"
  | .dMatchI x elemT outT f input => s!"dMatchI {x} {elemT} {outT}" ++ setNestAndLine 2 f.node.render ++ setNestAndLine 2 input.node.render
  | .seq c1 c2 => "seq " ++ setNestAndLine 2 c1.node.render ++ setNestAndLine 2 c2.node.render

-- modified from Nate
partial def DPIAPhraseNode.render : DPIAPhraseNode  → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .imperative i => s!"{i.render}"
  | .functional f => s!"{f.render}"
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render ++ Std.Format.line
    | .app .. , _       => f.node.render ++ " " ++ e.node.render ++ Std.Format.line
    | _       , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render ++ Std.Format.line
    | _       , _       => f.node.render ++ " " ++ e.node.render ++ Std.Format.line
  | .depapp f e   => f.node.render ++ " " ++ Std.Format.paren e.render ++ Std.Format.line
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | .pair fst snd => s!"({fst.node.render}, {snd.node.render})"
  | .proj1 p => s!"proj1 " ++ p.node.render
  | .proj2 p => s!"proj2 " ++ p.node.render
  | .ifThenElse cond thenP elseP => s!"if {cond.node.render}: \n {thenP.node.render}\n else: \n {elseP.node.render}" --TODO

end

instance : Std.ToFormat DPIAPhraseNode where
  format e := DPIAPhraseNode.render e

instance : ToString DPIAPhraseNode where
  toString e := Std.Format.pretty e.render

instance : Std.ToFormat ImperativePrimitives where
  format := ImperativePrimitives.render

instance : ToString ImperativePrimitives where
  toString e := Std.Format.pretty e.render

instance : Std.ToFormat FunctionalPrimitives where
  format := FunctionalPrimitives.render

instance : ToString FunctionalPrimitives where
  toString e := Std.Format.pretty e.render

-- copied from Nate
private def indent (s : String) : String :=
  s.trimAscii |>.split '\n' |>.toStringList |>.map (λ s => "  " ++ s) |> String.intercalate "\n"

-- modified from Nate
instance : ToString DPIAPhrase where
  toString e := "expr:\n" ++ (indent <| toString e.node) ++ "\ntype:\n" ++ (indent <| toString e.type)


partial def RExprNodeWith.renderPt : RExprNodePt → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .const s      => s.toString
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.renderPt ++ " " ++ Std.Format.paren e.node.renderPt
    | .app .. , _       => f.node.renderPt ++ " " ++ e.node.renderPt
    | _       , .app .. => f.node.renderPt ++ " " ++ Std.Format.paren e.node.renderPt
    | _       , _       => f.node.renderPt ++ " " ++ e.node.renderPt
  | .depapp f e   => f.node.renderPt ++ " " ++ Std.Format.paren e.render
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} =>{Std.Format.line}{b.node.renderPt}" ++ Std.Format.line
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} =>{Std.Format.line}{b.node.renderPt}" ++ Std.Format.line

instance : Std.ToFormat RExprNodePt where
  format := RExprNodeWith.renderPt

instance : ToString RExprNodePt where
  toString e := Std.Format.pretty e.renderPt

instance : ToString RExprPt where
  toString e := "expr:\n" ++ (indent <| toString e.node) ++ "\ntype:\n" ++ (indent <| toString e.type)
