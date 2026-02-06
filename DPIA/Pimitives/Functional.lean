import DPIA.Basic

def mkMap (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase) : DPIAPhrase :=
  let node := FunctionalPrimitives.map n s t a f array
  let type := PhraseType.acc (RData.array n t)
  {node := DPIAPhraseNode.functional node, type:= type : DPIAPhrase}
