import DPIA.Basic

def notContainingArrayType (composed : RData) : Bool :=
    match composed with
        | .scalar _ | .index _ | .natType | .vector _ _=> true
        | .pair fst snd => notContainingArrayType fst && notContainingArrayType snd
        | _ => false

partial def subTypeCheck (subType superType: PhraseType) : Bool :=
    if subType == superType then true
    else match (subType, superType) with
            | (PhraseType.expr bSub accessSub, PhraseType.expr bSuper _) =>
                if bSub == bSuper then accessSub == DAnnotation.read && notContainingArrayType bSub
                else false
            | (PhraseType.fn subInT subOutT, PhraseType.fn superInT superOutT) => subTypeCheck subInT superInT && subTypeCheck subOutT superOutT
            | (PhraseType.pi kind1 _ subOutT, PhraseType.pi kind2 _ superOutT) => kind1 == kind2 && subTypeCheck subOutT superOutT
            | _ => false
--termination_by phraseTypeSize subType + phraseTypeSize superType
