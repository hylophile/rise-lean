import DPIA.Compilation.TranslationToImperative
import DPIA.Compilation.Renaming
import C.Basic
import DPIA.ToC.CodeGenerator
import C.CModule
import DPIA.FromRise
import DPIA.Compilation.Renaming

private abbrev mkName := Lean.Name.mkSimple

-------- from functional DPIA to imperative DPIA ----------

def createOutputParam (outT : PhraseType) : DPIAPhrase :=
    match outT with
        | .expr dt _ => match dt with
                            | .scalar _ | .index _ | .natType | .vector _ _ => mkBvar 0 (mkName "output") (.acc (.array (.nat 1) dt))
                            | .array _ _ => mkBvar 0 (mkName "output") (.acc dt)
                            | .pair _ _ => panic! s!"pair types are not supported yet"
                            | _ => panic! s!"no other types supported. This should not have happened"
        | _ => panic! s!"the output parameter is supposed to be an expression type"

partial def splitBodyAndParams (p : DPIAPhrase) (ps : List DPIAPhrase) (depth : Nat) : (DPIAPhrase × (List DPIAPhrase)) :=
    match p with
        | ⟨.app fn arg, _⟩ => let sub := betaReduction fn arg
                              splitBodyAndParams sub ps depth
        | ⟨.depapp fn arg, _⟩ => let sub := dependentBetaReduction fn arg
                                 splitBodyAndParams sub ps depth
        | ⟨.lam name (.expr dt a) body, _⟩ => let param := mkBvar depth name (.expr dt a)
                                        splitBodyAndParams body (param :: ps) (depth+1)
        | ⟨.deplam name _ body,_⟩ => let param := mkBvar depth name (.expr (.scalar .int) .read)
                                     splitBodyAndParams body (param :: ps) (depth + 1) -- check again the name
        | ⟨_, .expr _ _⟩ => (p, ps.reverse)
        | ⟨_, _⟩ => panic! s!"this should not happen"

partial def splitBodyAndParamsWithParams (p : DPIAPhrase) (ps : List (DPIAPhrase × String)) (depth : Nat) : (DPIAPhrase × (List (DPIAPhrase × String))) :=
    match p with
        | ⟨.app fn arg, _⟩ => let sub := betaReduction fn arg
                              splitBodyAndParamsWithParams sub ps depth
        | ⟨.depapp fn arg, _⟩ => let sub := dependentBetaReduction fn arg
                                 splitBodyAndParamsWithParams sub ps depth
        | ⟨.lam name (.expr dt a) body, _⟩ => let param := mkBvar depth name (.expr dt a)
                                        splitBodyAndParamsWithParams body ((param, "fn") :: ps) (depth+1)
        | ⟨.deplam name _ body,_⟩ => let param := mkBvar depth name (.expr (.scalar .int) .read)
                                     splitBodyAndParamsWithParams body ((param, "pi") :: ps) (depth + 1) -- check again the name
        | ⟨_, .expr _ _⟩ => (p, ps.reverse)
        | ⟨_, _⟩ => panic! s!"this should not happen"

-- check that output parameter is correctly created
def matchOutputType (outType pType : RData) (outParam : DPIAPhrase) : DPIAPhrase :=
    if outType == pType then outParam
    else match outType, pType with
            | .array (.nat 1) lhsT, rhsT => if lhsT == rhsT
                                                then atAcc  outParam (mkFunctional (.expr (.index (.nat 1)) .read)
                                                                                   (.natAsIndex (.nat 1) {node := .natural (.nat 0), type := .expr .natType .read}))
                                                else panic! s!"{lhsT} and {rhsT} should match"
            | _, _ => panic! s!"{outType} and {pType} should match"

-- takes functioal DPIA Phrase and output parameter and returns imperative DPIA
partial def toImperative (outParam p : DPIAPhrase) : DPIAPhrase :=
    let output := matchOutputType (getDataType outParam.type) (getDataType p.type) outParam
    acc p output 0


-- hole pipeline  in: functional DPIA
--                --> split function parameters -> create a parameter to write into
--                out: list of DPIA Parameters and imperative DPIA body
partial def applyToImp (p : DPIAPhrase) : List DPIAPhrase :=
    let (body, params) := splitBodyAndParams p [] 0
    let outParam := createOutputParam body.type
    let expr := toImperative outParam body
    outParam :: params.concat expr

partial def applyToImpWithRenaming (p : DPIAPhrase) : List (DPIAPhrase × String) :=
    let (body, params) := splitBodyAndParamsWithParams p [] 0
    let outParam := createOutputParam body.type
    let expr := toImperative outParam body
    (outParam, "fn") :: params.concat (expr, "body")

----- from DPIA to CStmt

-- "remember" all input parameters
def insertDeclToEnv (ps : List DPIAPhrase) (map : Std.HashMap Lean.Name CExpr) : (DPIAPhrase × Std.HashMap Lean.Name CExpr) :=
    match ps with
        | [] => panic! s!"there should be at least one element in the list!"
        | x :: [] => (x, map)
        | ⟨.bvar _ n, _⟩ :: ys => insertDeclToEnv ys (map.insert n (.declRef n))
        | _ => panic! s!"there should only be one phrase in the list that is not a identifier"

partial def generateCode (ps : List DPIAPhrase) : CStmt :=
    let (phrase, indentEnv) := insertDeclToEnv ps {}
    let env := mkEnv indentEnv {} {}
    generateWithFunctions env phrase

-------- from CStmt to CModule
def makeParamTy (dt : RData) : CType :=
    match dt with
        | .array _ elemT => let baseDt := getBaseDataType elemT
                            .pointer (typ baseDt)
        |.pair _ _ => typ dt
        | .scalar _ => typ dt
        | .natType => typ dt
        | .index _ => typ dt
        | _ => panic! s!"did not expect {dt}"

def makeParam (param : DPIAPhrase) : CDecl :=
    match param with
        | ⟨.bvar _ name, pt⟩ => .param name (makeParamTy (getDataType pt))
        | _ => panic! s!"for making declarations, only identifiers are accepted!"

partial def makeCModule (cS : CStmt) (params : List DPIAPhrase) : Module :=
    let cParams := params.map makeParam
    let includes := [IncludeDirective.includeHeader "stdint.h"]
    let decls := []
    let function := CDecl.fn (mkName "foo") (.scalar (.void)) cParams cS
    {includes := includes, decls := decls, functions := [{code := function}]}


-------- Piplen RExpr -> CModule ------------

-- hole pipline, takes a RISE expression and returns a CModule
partial def CCodeFromRise (rise : RExpr) : Module :=
    let phrases := fromRise rise |>
                        applyToImpWithRenaming |>
                            uniqueRenamingWithParams
    let cStmt := generateCode phrases
    makeCModule cStmt phrases.dropLast
