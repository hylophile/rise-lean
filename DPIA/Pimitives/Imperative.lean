import DPIA.Basic

-- vector ops
def mkAsScalarAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.asScalarAcc n m t array
  let type := PhraseType.acc (RData.array m (RData.vector n t))
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkAssign (t : RData) (lhs rhs : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.assign t lhs rhs
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkAsVectorAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.asVectorAcc n m t array
  let type := PhraseType.acc (RData.array (RNat.mult n m) t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}


  -- for ops
def mkForLoop (unroll : Bool) (n : RNat) (body : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.forLoop unroll n body
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkForNat (unroll : Bool) (n : RNat) (body : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.forNat unroll n body
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkForVec (n : RNat) (t : RData) (out body : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.forVec n t out body
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}


  -- array ops
def mkGenerateCont (n : RNat) (t : RData) (f : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.generateCont n t f
  let type := PhraseType.expr (RData.array n t) DAnnotation.read
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkIdxAcc (n : RNat) (t : RData) (idx array: DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.idxAcc n t idx array
  let type := PhraseType.acc t
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkIdxVecAcc(n : RNat) (t : RData) (idx vec : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.idxVecAcc n t idx vec
  let type := PhraseType.acc t
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkScatterAcc (n m : RNat) (t : RData) (indicies array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.scatterAcc n m t indicies array
  let type := PhraseType.acc (RData.array (RNat.mult n m) t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkSplitAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.splitAcc n m t  array
  let type := PhraseType.acc (RData.array (RNat.mult n m) t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkJoinAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.joinAcc n m t array
  let type := PhraseType.acc (RData.array n (RData.array m t))
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkUnzipAcc (n : RNat) (t1 t2 : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.unzipAcc n t1 t2 array
  let type := PhraseType.acc (RData.array n (RData.pair t1 t2))
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkZipAcc1 (n : RNat) (t1 t2 : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.zipAcc1 n t1 t2 array
  let type := PhraseType.acc (RData.array n t1)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkZipAcc2 (n : RNat) (t1 t2 : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.zipAcc2 n t1 t2 array
  let type := PhraseType.acc (RData.array n t2)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkTransposeAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.transposeAcc n m t array
  let type := PhraseType.acc (RData.array n (RData.array m t))
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkCycleAcc (n m : RNat) (t : RData) (input : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.cycleAcc n m t input
  let type := PhraseType.acc (RData.array n t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkReorderAcc (n idxF : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase := -- NatToNat? (idxF : natToNat)
  let node := ImperativePrimitives.reorderAcc n idxF t array
  let type := PhraseType.acc (RData.array n t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkDropAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.dropAcc n m t array
  let type := PhraseType.acc (RData.array (RNat.minus m n) t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkTakeAcc (n m : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.takeAcc n m t array
  let type := PhraseType.acc (RData.array n t)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}


-- map ops
def mkMapAcc (n : RNat) (t1 t2 t3 : RData) (f array : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.mapAcc t1 t2 t3 f array
  let type := PhraseType.acc (RData.array n t2)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkMapFstAcc (t1 t2 t3 : RData) (f record : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.mapFstAcc t1 t2 t3 f record
  let type := PhraseType.acc (RData.pair t1 t2)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkMapRead (n : RNat) (t1 t2 t3 : RData) (f input : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.mapRead n t1 t2 t3 f input
  let type := PhraseType.expr (RData.array n t2) DAnnotation.read
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkMapSndAcc (t1 t2 t3 : RData) (f record : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.mapSndAcc t1 t2 t3 f record
  let type := PhraseType.acc (RData.pair t1 t2)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



-- pair ops
-- def mkMkDPairFstl (fst : RNat) (a : DPIAPhrase) : DPIAPhrase :=
--   let node := ImperativePrimitives.mkDPairFstl fst a
--   let type :=
--   {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

-- def mkMkDPairSndAcc (fst : RNat) (sndT : RData) (a : DPIAPhrase) : DPIAPhrase := --TODO: what does it do?
--   let node := ImperativePrimitives.mkDPairSndAcc fst sndT a
--   let type :=
--   {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkPairAcc (t1 t2 : RData) (fst snd : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.pairAcc t1 t2 fst snd
  let type := PhraseType.acc (RData.pair t1 t2)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkPairAcc1 (t1 t2 : RData) (pair : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.pairAcc1 t1 t2 pair
  let type := PhraseType.acc t1
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkPairAcc2 (t1 t2 : RData) (pair : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.pairAcc2 t1 t2 pair
  let type := PhraseType.acc t2
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

-- memory ops
def mkNew (t : RData) (f : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.new t f
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkNewDoubleBuffer (n : RNat) (t1 t2 t3 : RData) (input out f : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.newDoubleBuffer n t1 t2 t3 input out f
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}



def mkComment (comment : String) : DPIAPhrase :=
  let node := ImperativePrimitives.comment comment
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkSkip : DPIAPhrase :=
  let node := ImperativePrimitives.skip
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}


  -- ? TODO
def mkDepIdxAcc (n idx ft: RNat) (array : DPIAPhrase) : DPIAPhrase := -- NatToNat? (ft : natToNat)
  let node := ImperativePrimitives.depIdxAcc n idx ft array
  let type := PhraseType.acc RData.natType
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkDepJoinAcc (n lenF : RNat) (t : RData) (array : DPIAPhrase) : DPIAPhrase := -- NatToNat? (lenF : natToNat)
  let node := ImperativePrimitives.depJoinAcc n lenF t array
  let type := PhraseType.acc (RData.array n RData.natType)
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

-- def mkDMatchI (x : RNat) (elemT outT : RData) (f input : DPIAPhrase) : DPIAPhrase := -- NatIdentifier? (x : natIdentifier)
--   let node := ImperativePrimitives.dMatchI x elemT outT f input
--   let type :=
--   {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}

def mkSeq (c1 c2 : DPIAPhrase) : DPIAPhrase :=
  let node := ImperativePrimitives.seq c1 c2
  let type := PhraseType.comm
  {node := DPIAPhraseNode.imperative node, type := type : DPIAPhrase}
