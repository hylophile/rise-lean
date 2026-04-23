import DPIA.Pimitives.Imperative
import DPIA.Pimitives.Functional

def fst (pair : DPIAPhrase) : DPIAPhrase :=
    match pair.type with
        | .expr (.pair dt1 dt2) _ => mkFst dt1 dt2 pair
        | _ => panic! s!"no valid pair type: {pair.type}"

def snd (pair : DPIAPhrase) : DPIAPhrase :=
    match pair.type with
        | .expr (.pair dt1 dt2) _ => mkFst dt1 dt2 pair
        | _ => panic! s!"no valid pair type: {pair.type}"

-- create an assign statement in the way that C accepts
def assignByType (dt : RData) (lhs rhs : DPIAPhrase) : DPIAPhrase :=
    match dt with
        | .scalar _ | .natType | .index _ => mkAssign dt lhs rhs
        | .pair dt1 dt2 => mkSeq (mkAssign dt1  (mkPairAcc1 dt1 dt2 lhs)
                                                (fst rhs))
                                 (mkAssign dt2  (mkPairAcc2 dt1 dt2 lhs)
                                                (snd rhs))
        | _ => panic! s!"Don't know how to assign value of type {dt}"
