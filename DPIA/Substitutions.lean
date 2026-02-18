import DPIA.Basic

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

def phraseTypeSize (pt : PhraseType) : Nat :=
  match pt with
    | .expr _ _ => 1
    | .comm => 1
    | .acc _ => 1
    | .pi _ _ body => 1 + phraseTypeSize body
    | .fn binderType body => 1 +  phraseTypeSize binderType + phraseTypeSize body
    | .phrasePair p1 p2 => 1 + phraseTypeSize p1 + phraseTypeSize p2
