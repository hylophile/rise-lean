import DPIA.Basic

def mkLam (type : PhraseType) (name : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .lam name binderType body, type := type : DPIAPhrase}

def mkApp (type : PhraseType) (fn arg : DPIAPhrase) : DPIAPhrase :=
    {node := .app fn arg, type := type : DPIAPhrase}

def mkDeplam (type : PhraseType) (name : Lean.Name) (binderKind : DKind) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .deplam name binderKind body, type := type : DPIAPhrase}

def mkBvar (index : Nat) (name : Lean.Name) (type : PhraseType) : DPIAPhrase :=
  {node := .bvar index name, type := type : DPIAPhrase}
