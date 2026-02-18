import DPIA.Basic

def mkId (t : RData) (a : DAnnotation) : DPIAPhrase :=
  let node := FunctionalPrimitives.id t
  let type := PhraseType.expr t a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkNeg (t : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.neg t
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

  -- binary ops
def mkAdd (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.add lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkSub (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.sub lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMul (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.mul lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkDiv (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.div lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMod (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.mod lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- ternary ops
def mkSelect (t : RData) (cond : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.select t cond
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- comparison ops
def mkNot (v : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.not v
  let type := PhraseType.expr v DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkGt (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.gt lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkLt (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.lt lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkEqual (lhs rhs : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.equal lhs rhs
  let type := PhraseType.expr lhs DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

  -- cast ops
def mkCast (s t : RData) : DPIAPhrase :=
  let node := FunctionalPrimitives.cast s t
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkIndexAsNat (n : RNat) (idx : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.indexAsNat n idx
  let type := PhraseType.expr RData.natType DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkNatAsIndex (n : RNat) (idx : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.natAsIndex n idx
  let type := PhraseType.expr (RData.index n) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

  -- memory ops
def mkRlet (s t : RData) (a : DAnnotation) (f val: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.rlet s t a f val
  let type := PhraseType.expr t a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkToMem (t : RData) (input : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.toMem t input
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

  -- array ops
def mkGenerate (n : RNat) (t : RData) (f : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.generate n t f
  let type := PhraseType.expr (RData.array n t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkIdx (n : RNat) (t : RData) (idx array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.idx n t idx array
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkDepIdx (n idx : RNat) (ft : NatToData) (array : DPIAPhrase) : DPIAPhrase := -- TODO
--   let node := FunctionalPrimitives.depIdx n idx ft array
--   let type := PhraseType.expr (ft.apply idx) DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkIdxVec (n : RNat) (t : RData) (idx vec : DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.idxVec n t idx vec
--   let type := PhraseType.expr t DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


def mkTake (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.take n m t array
  let type := PhraseType.expr (RData.array n t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkDrop (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.drop n m t array
  let type := PhraseType.expr (RData.array m t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkConcat (n m : RNat) (t : RData) (nArray mArray : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.concat n m t nArray mArray
  let type := PhraseType.expr (RData.array (RNat.plus n m) t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}



def mkSplit (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.split n m t a array
  let type := PhraseType.expr (RData.array m (RData.array n t)) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkJoin (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.join n m t a array
  let type := PhraseType.expr (RData.array (RNat.mult n m) t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


def mkSlide (n sz sp : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.slide n sz sp t array
  let type := PhraseType.expr (RData.array (RNat.plus (RNat.nat 1) n) (RData.array sz t)) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkCircularBuffer (n alloc sz : RNat) (s t : RData) (load array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.circularBuffer n alloc sz s t load array
  let type := PhraseType.expr (RData.array n (RData.array sz t)) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkRotatevalues (n sz : RNat) (t : RData) (wrt array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.rotateValues n sz t wrt array
  let type := PhraseType.expr (RData.array n (RData.array sz t)) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}



def mkTranspose (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.transpose n m t a array
  let type := PhraseType.expr (RData.array n (RData.array m t)) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkCycle (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.cycle n m t array
--   let type := PhraseType.expr (RData.array m t) DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkReorder (n : RNat) (idxF : NatToNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.reorder n idxF t a array
--   let type := PhraseType.expr (RData.array n t) a
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkTransposeDepArray (n m : RNat) (ft : NatToData) (array : DPIAPhrase) : DPIAPhrase := --TODO type = exp[n..(i: nat |-> n.ft(i)), read]
--   let node := FunctionalPrimitives.transposeDepArray n m ft array
--   let type := PhraseType.expr (RData.array n ) DAnnotation.read --> noch nicht korrekt!
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}
--> needs dependent array



def mkGather (n m : RNat) (t : RData) (idx array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.gather n m t idx array
  let type := PhraseType.expr (RData.array n t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkScatter (n m : RNat) (t : RData) (idx array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.scatter n m t idx array
  let type := PhraseType.expr (RData.array m t) DAnnotation.write
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}



def mkPadCst (n l r : RNat) (t : RData) (padExpr array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.padCst n l r t padExpr array
  let type := PhraseType.expr (RData.array (RNat.plus l (RNat.plus n r)) t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkPadClamp (n l r : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.padClamp n l r t array
  let type := PhraseType.expr (RData.array (RNat.plus l (RNat.plus n r)) t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkPadEmpty (n r : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.padEmpty n r t array
  let type := PhraseType.expr (RData.array  (RNat.plus n r) t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}



def mkZip (n : RNat) (s t : RData) (a : DAnnotation) (sArray tArray : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.zip n s t a sArray tArray
  let type := PhraseType.expr (RData.array n (RData.pair s t)) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkUnzip (n : RNat) (s t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.unzip n s t a array
  let type := PhraseType.expr (RData.pair (RData.array n s) (RData.array n t)) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkDepZip (n : RNat) (ft1 ft2 : NatToData) (e1 e2 : DPIAPhrase) : DPIAPhrase := -- TODO  exp[n..(i: nat |-> (ft1(i), ft2(i)) ), read]
--   let node := FunctionalPrimitives.depZip n ft1 ft2 e1 e2
--   let type := PhraseType.expr (RData.array n RData.natType) DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


-- not in current Rise Implementation

-- def mkMakeArray (n : RNat) (t : RData) (elements : List DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.makeArray n t elements
--   let type := PhraseType.expr (RData.array n t) DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkPartition (n m : RNat) (lenF : NatToNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase := -- TODO exp[m..(i: nat |-> lenF(i).dt), read]
--   let node := FunctionalPrimitives.partition n m lenF t array
--   let type := PhraseType.expr (RData.array m RData.natType) DAnnotation.read
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}
--> braucht dependent array length


  -- pair ops

def mkMakePair (s t : RData) (a : DAnnotation) (fst snd : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.makePair s t a fst snd
  let type := PhraseType.expr (RData.pair s t) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkMakeDepPair (fst : RNat) (sndT : RData) (a : DAnnotation) (snd : DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.makeDepPair fst sndT a snd
--   let type := PhraseType.expr

def mkFst (s t : RData) (pair : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.fst s t pair
  let type := PhraseType.expr s DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkSnd (s t : RData) (pair : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.snd s t pair
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


-- vector ops
def mkVectorFromScalar (n : RNat) (t : RData) (arg : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.vectorFromScalar n t arg
  let type := PhraseType.expr (RData.vector n t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkAsVector (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.asVector n m t a array
  let type := PhraseType.expr (RData.array m (RData.vector n t)) a
  {node := DPIAPhraseNode.functional node, type := type : DPIAPhrase}

def mkAsVectorAligned (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.asVectorAligned n m t a array
  let type := PhraseType.expr (RData.array m (RData.vector n t)) a
  {node := DPIAPhraseNode.functional node, type := type : DPIAPhrase}

def mkAsScalar (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.asScalar n m t a array
  let type := PhraseType.expr (RData.array (RNat.mult n m) t) a
  {node := DPIAPhraseNode.functional node, type := type : DPIAPhrase}

-- map

-- def mkMap (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.map n s t a f array
--   let type := PhraseType.acc (RData.array n t)
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMap (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.map n s t a f array
  let type := PhraseType.expr (RData.array n t) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMapSeq (unroll : Bool) (n : RNat) (s t : RData) (f array: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.mapSeq unroll n s t f array
  let type := PhraseType.expr (RData.array n t) DAnnotation.write
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMapStream (n : RNat) (s t : RData) (f array: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.mapStream n s t f array
  let type := PhraseType.expr (RData.array n t) DAnnotation.write
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkIterateStream (n : RNat) (s t : RData) (f array: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.iterateStream n s t f array
  let type := PhraseType.expr (RData.array n t) DAnnotation.write
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkDepMapSeq (unroll : Bool) (n : RNat) (ft1 ft2 : NatToData) (f array: DPIAPhrase) : DPIAPhrase := -- TODO
--   let node := FunctionalPrimitives.depMapSeq unroll n ft1 ft2 f array
--   let type := PhraseType.expr (RData.array n RData.natType) DAnnotation.write
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- not in current Rise Implementation

-- def mkMapVec (n : RNat) (t1 t2 : RData) (f vec : DPIAPhrase) : DPIAPhrase :=
--   let node := FunctionalPrimitives.mapVec n t1 t2 f vec
--   let type := PhraseType.expr (RData.vector n t2) DAnnotation.write
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMapFst (s1 t s2 : RData) (a : DAnnotation) (f pair : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.mapFst s1 t s2 a f pair
  let type := PhraseType.expr (RData.pair t s2) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

def mkMapSnd (s t1 t2 : RData) (a : DAnnotation) (f pair : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.mapSnd s t1 t2 a f pair
  let type := PhraseType.expr (RData.pair s t2) a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- reduce
def mkReduceSeq (unroll : Bool) (n : RNat) (s t : RData) (f init array : DPIAPhrase ) : DPIAPhrase :=
  let node := FunctionalPrimitives.reduceSeq unroll n s t f init array
  let type := PhraseType.expr t DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


  -- scan
def mkScanSeq (n :RNat) (s t : RData) (f init array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.scanSeq n s t f init array
  let type := PhraseType.expr (RData.array n t) DAnnotation.read
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


  -- iterate
def mkIterate (n m k : RNat) (t : RData) (f array : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.iterate n m k t f array
  let type := PhraseType.expr (RData.array m t) DAnnotation.write
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


-- not in current Rise Implementation

-- def mkDepTile (n tileSize haloSize : RNat) (t1 t2 : RData) (processTiles array : DPIAPhrase) : DPIAPhrase := --TODO
--   let node := FunctionalPrimitives.depTile n tileSize haloSize t1 t2 processTiles array
--   let type :=
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}

-- def mkDMatch (x : RNat) (elemT outT : RData) (a : DAnnotation) (f array : DPIAPhrase) : DPIAPhrase := -- TODO (x : NatIdentifier)
--   let node := FunctionalPrimitives.dMatch x elemT ouT a f array
--   let type :=
--   {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}


def mkPrintType (msg : String) (t : RData) (a : DAnnotation) (input : DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.printType msg t a input
  let type := PhraseType.expr t a
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}
