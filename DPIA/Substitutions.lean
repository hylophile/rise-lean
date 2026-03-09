import DPIA.Basic
import Rise.Basic

-- substitute annotations in Dannotations
def substituteAnnotationA (a : DAnnotation) (name : Lean.Name) (key : DAnnotation) : DAnnotation :=
  match a with
    | .identifier userName => if userName == name then key else a
    | .read => a
    | .write => a

-- substitute annotations in PhraseTypes
def substituteAnnotationPt (pt : PhraseType) (name : Lean.Name) (key : DAnnotation) : PhraseType :=
  match pt with
    | .expr dt rw => PhraseType.expr dt (substituteAnnotationA rw name key)
    | .comm => pt
    | .acc _ => pt
    | .pi binderKind userName body => PhraseType.pi binderKind userName (substituteAnnotationPt body name key)
    | .fn binderType body => PhraseType.fn (substituteAnnotationPt binderType name key) (substituteAnnotationPt body name key)
    | .phrasePair p1 p2 => PhraseType.phrasePair (substituteAnnotationPt p1 name key) (substituteAnnotationPt p2 name key)

def substituteDataInData (dt : RData) (For : Lean.Name) (In : RData) : RData :=
  match In with
    | .bvar _ userName => if userName == For then dt else In --> not sure how to include deBruijnIndex yet --> need to take a look at it again
    | .array n aDt => RData.array n (substituteDataInData dt For aDt)
    | .pair p1 p2 => RData.pair (substituteDataInData dt For p1) (substituteDataInData dt For p2)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => RData.vector n (substituteDataInData dt For vDt)
    | _ => panic! s!"that should never happen"

def substituteDataInPhraseType (sN : RData) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  match In with
    | .expr dt rw => let nDt := substituteDataInData sN For dt
                    PhraseType.expr nDt rw
    | .comm => In
    | .acc dt => let nDt := substituteDataInData sN For dt
                PhraseType.acc nDt
    | .pi binderKind userName body => let nBody := substituteDataInPhraseType sN For body
                                     PhraseType.pi binderKind userName nBody
    | .fn binderType body => let nBinderType := substituteDataInPhraseType sN For binderType
                            let nBody := substituteDataInPhraseType sN For body
                            PhraseType.fn nBinderType nBody
    | .phrasePair p1 p2 => let nP1 := substituteDataInPhraseType sN For p1
                          let nP2 := substituteDataInPhraseType sN For p2
                          PhraseType.phrasePair nP1 nP2

def substituteNatInData (n : RNat) (For : Lean.Name) (In : RData) : RData :=
  match In with
    | .bvar _ userName => if userName == For then RData.natType else In
    | .array n aDt => RData.array n (substituteNatInData n For aDt)
    | .pair p1 p2 => RData.pair (substituteNatInData n For p1) (substituteNatInData n For p2)
    | .index _ => In
    | .scalar _ => In
    | .natType => In
    | .vector n vDt => RData.vector n (substituteNatInData n For vDt)
    | _ => panic! s!"that should never happen"

def substituteNatInPhraseType (sN : RNat) (For : Lean.Name) (In : PhraseType) : PhraseType :=
  match In with
    | .expr dt rw => let nDt := substituteNatInData sN For dt
                    PhraseType.expr nDt rw
    | .comm => In
    | .acc dt => let nDt := substituteNatInData sN For dt
                PhraseType.acc nDt
    | .pi binderKind userName body => let nBody := substituteNatInPhraseType sN For body
                                     PhraseType.pi binderKind userName nBody
    | .fn binderType body => let nBinderType := substituteNatInPhraseType sN For binderType
                            let nBody := substituteNatInPhraseType sN For body
                            PhraseType.fn nBinderType nBody
    | .phrasePair p1 p2 => let nP1 := substituteNatInPhraseType sN For p1
                          let nP2 := substituteNatInPhraseType sN For p2
                          PhraseType.phrasePair nP1 nP2


-- def matchTypeDependentOnKind (k : DKind) : Type :=
--   match k with
--     | .rise r => match r with
--                   | .data => RData
--                   | .nat => RNat
--                   | _ => panic! s!"cannot return a Type"
--     | .readWrite => DAnnotation
--     | _ => panic! s!"cannot return a Type"


-- substitute kinds in PhraseTypes
-- def substituteKindsPt {T : Type} (binderKind : DKind) (x : matchTypeDependentOnKind binderKind) (For : Lean.Name) (In : PhraseType) : PhraseType :=
--   match binderKind, x with
--     | DKind.rise RKind.data , (x : RData) => substituteDataPt x For In
--     | DKind.rise RKind.nat , (x : RNat) => substituteNatPt x For In
--     | DKind.readWrite, (x : DAnnotation) => substituteAnnotationPt In For x
--     | _, _ => panic! s!"could not substitute x in {For}"

def phraseTypeSize (pt : PhraseType) : Nat :=
  match pt with
    | .expr _ _ => 1
    | .comm => 1
    | .acc _ => 1
    | .pi _ _ body => 1 + phraseTypeSize body
    | .fn binderType body => 1 +  phraseTypeSize binderType + phraseTypeSize body
    | .phrasePair p1 p2 => 1 + phraseTypeSize p1 + phraseTypeSize p2


def TypedRExprSize (rt : TypedRExpr) : Nat :=
  match rt with
    | ⟨.bvar _ _,_⟩ => 1
    | ⟨.const _,_⟩ => 1
    | ⟨.lit _, _⟩ => 1
    | ⟨.app fn arg,_⟩ => 1 + TypedRExprSize fn + TypedRExprSize arg
    | ⟨.depapp fn _,_⟩ => 1 + TypedRExprSize fn
    | ⟨.lam _ _ body,_⟩ => 1 + TypedRExprSize body
    | ⟨.deplam _ _ body,_⟩ => 1 + TypedRExprSize body
    | _ => 1
