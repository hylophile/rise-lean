import DPIA.Basic

-- recursivlely checks wheather array type is present in given data type;
-- returns true if not present
def notContainingArrayType (composed : RData) : Bool :=
    match composed with
        | .scalar _ | .index _ | .natType | .vector _ _=> true
        | .pair fst snd => notContainingArrayType fst && notContainingArrayType snd
        | _ => false

-- returns true if subType <= superType
partial def subTypeCheck (subType superType: PhraseType) : Bool :=
    if subType == superType then true
    else match (subType, superType) with
            | (.expr bSub accessSub, .expr bSuper _) =>
                if bSub == bSuper then accessSub == .read && notContainingArrayType bSub
                else false
            | (.fn subInT subOutT, .fn superInT superOutT) => subTypeCheck subInT superInT && subTypeCheck subOutT superOutT
            | (.pi kind1 _ subOutT, .pi kind2 _ superOutT) => kind1 == kind2 && subTypeCheck subOutT superOutT
            | _ => false

-- returns data and ensures that RType is data
def assertDataType (exprT: RType) : RData :=
  match exprT with
    | .data dt => dt
    | _ => panic! s!"THis should never happen"

-- returns the argument type of a function and ensures that RType is a function type
def assertFunctionType (exprT: RType) : RType :=
  match exprT with
    | .fn inT _ => inT
    | _ => panic! s!"THis should never happen"

-- retruns the base type of nested data types
def getBaseDataType (dt : RData) : RData :=
  match dt with
    | .scalar _ | .index _ | .vector _ _ => dt
    | .pair _ _=> dt
    | .bvar _ _ => dt
    | .array _ elemT =>  getBaseDataType elemT
    | _ => panic! s!"there should not be any mvars anymore!"

-- returns the data type to a phrase type
def getDataType (exprT: PhraseType) : RData :=
  match exprT with
    | .expr dt _ => dt
    | .acc dt => dt
    | .pi _ _ body => getDataType body
    | .fn _ body => getDataType body
    | _ => panic! s!"this should not happen, cannot determine the datatype"

def getDt (pt : PhraseType) : RData :=
    match pt with
        | .expr dt _ => dt
        | .acc dt => dt
        | .phrasePair (.expr dt1 _) (.acc dt2) => if dt1 == dt2 then dt1
                                                  else panic! s!"the data types {dt1} and {dt2} should match!"
        | _ => panic! s!"this should not happen, only expr, acc and pairs are allowed"
