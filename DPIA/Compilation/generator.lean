import DPIA.Compilation.TranslationToImperative
import DPIA.Compilation.Renaming

private abbrev mkName := Lean.Name.mkSimple

def createOutputParam (outT : PhraseType) : DPIAPhrase :=
    match outT with
        | .expr dt _ => match dt with
                            | .scalar _ | .index _ | .natType | .vector _ _ => mkBvar 0 (mkName "output") (.acc (.array (.nat 1) dt))
                            | .array _ _ => mkBvar 0 (mkName "output") (.acc dt)
                            | .pair _ _ => panic! s!"pair types are currently not supported"
                            | _ => panic! s!"no other types supported. This should not have happened"
        | _ => panic! s!"the output parameter is supposed to be an expression type"

partial def splitBodyAndParams (p : DPIAPhrase) (ps : List DPIAPhrase) (depth : Nat) : (DPIAPhrase × (List DPIAPhrase)) :=
    match p with
        | ⟨.app fn arg, _⟩ => let sub := betaReduction fn arg
                              splitBodyAndParams sub ps depth
        | ⟨.depapp fn arg, _⟩ => let sub := dependentBetaReduction fn arg
                                 splitBodyAndParams sub ps depth
        | ⟨.lam name (.expr dt a) body, _⟩ => let param := mkBvar depth name (.expr dt a)
                                        splitBodyAndParams body (param:: ps) (depth+1)
        | ⟨.deplam name _ body,_⟩ => let param := mkBvar depth name (.expr (.scalar .int) .read)
                                     splitBodyAndParams body (param :: ps) (depth + 1) -- check again the name
        | ⟨_, .expr _ _⟩ => (p, ps.reverse)
        | ⟨_, _⟩ => panic! s!"this should not happen"

def matchOutputType (outType pType : RData) (outParam : DPIAPhrase) : DPIAPhrase :=
    if outType == pType then outParam
    else match outType, pType with
            | .array (.nat 1) lhsT, rhsT => if lhsT == rhsT
                                                then atAcc  outParam
                                                            (mkFunctional (.expr (.index (.nat 1)) .read)
                                                                          (.natAsIndex (.nat 1) {node := .lit (.int 1), type := .expr .natType .read}))
                                                else panic! s!"{lhsT} and {rhsT} should match"
            | _, _ => panic! s!"{outType} and {pType} should match"

partial def toImperative (outParam p : DPIAPhrase) : DPIAPhrase :=
    let output := matchOutputType (getDataType outParam.type) (getDataType p.type) outParam
    acc p output 0


partial def applyToImp (p : DPIAPhrase ) : List DPIAPhrase:= --for testing the acc function
    --let renamed := uniqueRenaming p
    let (body, params) := splitBodyAndParams p [] 0
    let outParam := createOutputParam body.type
    let expr := toImperative outParam body
    expr :: params
