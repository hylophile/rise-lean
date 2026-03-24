import DPIA.Basic

def mkLam (type : PhraseType) (name : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .lam name binderType body, type := type : DPIAPhrase}

def mkApp (type : PhraseType) (fn arg : DPIAPhrase) : DPIAPhrase :=
    {node := .app fn arg, type := type : DPIAPhrase}

def mkDeplam (type : PhraseType) (name : Lean.Name) (binderKind : DKind) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .deplam name binderKind body, type := type : DPIAPhrase}

def mkBvar (index : Nat) (name : Lean.Name) (type : PhraseType) : DPIAPhrase :=
  {node := .bvar index name, type := type : DPIAPhrase}

def mkProj1 (type : PhraseType) (p : DPIAPhrase) : DPIAPhrase :=
  {node := .proj1 p, type := type : DPIAPhrase}

def mkProj2 (type : PhraseType) (p : DPIAPhrase) : DPIAPhrase :=
  {node := .proj2 p, type := type : DPIAPhrase}

def mkIfThenElse (type : PhraseType) (cond thenP elseP : DPIAPhrase) : DPIAPhrase :=
  {node := .ifThenElse cond thenP elseP, type := type : DPIAPhrase}

def mkFunctional (type : PhraseType) (func : FunctionalPrimitives) : DPIAPhrase :=
  {node := .functional func, type := type}
