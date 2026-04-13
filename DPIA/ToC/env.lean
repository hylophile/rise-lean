import C.Basic

structure Environment where
    identEnv: Std.HashMap (Lean.Name × Nat) CExpr
    commEnv: Std.HashMap (Lean.Name × Nat) CStmt
    contEnv: Std.HashMap (Lean.Name × Nat) (DPIAPhrase  → CStmt)
    letNatEnv: Std.HashMap (Lean.Name × Nat) DPIAPhrase

def updatedIdentEnv (e : Environment) (kv : Lean.Name) (n : Nat) (c : CExpr) : Environment :=
    {identEnv := e.identEnv.insert (kv, n) c
     commEnv := e.commEnv
     contEnv := e.contEnv
     letNatEnv := e.letNatEnv}

def lookUpIdentEnv (e: Environment) (kv : Lean.Name) (n : Nat) : CExpr :=
    match e.identEnv.get? (kv, n) with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"

def updatedCommEnv (e : Environment) (kv : Lean.Name) (n : Nat) (c : CStmt) : Environment :=
    {identEnv := e.identEnv
     commEnv := e.commEnv.insert (kv, n) c
     contEnv := e.contEnv
     letNatEnv := e.letNatEnv}

def lookUpCommEnv  (e: Environment) (kv : Lean.Name) (n : Nat) : CStmt :=
    match e.commEnv.get? (kv, n) with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"

def updatedContEnv (e : Environment) (kv : Lean.Name) (n : Nat) (f : DPIAPhrase  → CStmt) : Environment :=
    {identEnv := e.identEnv
     commEnv := e.commEnv
     contEnv := e.contEnv.insert (kv, n) f
     letNatEnv := e.letNatEnv}

def lookUpContEnv  (e: Environment) (kv : Lean.Name) (n : Nat) : DPIAPhrase  → CStmt :=
    match e.contEnv.get? (kv, n) with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"


def updatedNatEnv (e : Environment) (kv : Lean.Name) (n : Nat) (p : DPIAPhrase) : Environment :=
    {identEnv := e.identEnv
     commEnv := e.commEnv
     contEnv := e.contEnv
     letNatEnv := e.letNatEnv.insert (kv, n) p}

def lookUpNatEnv  (e: Environment) (kv : Lean.Name) (n : Nat) : DPIAPhrase :=
    match e.letNatEnv.get? (kv, n) with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"


inductive PairAccess where
    | fstMember
    | sndMember

inductive PathExpr where
    | pairAccess (a : PairAccess)
    | cIntExpr (num : RNat)
    | dPairSnd

instance : ToString PairAccess where
    toString
      | .fstMember => "fstMember"
      | .sndMember => "sndMember"

instance : ToString PathExpr where
  toString
    | .pairAccess a => s!"{a}"
    | .cIntExpr num => s!"cIntExpr {num}"
    | .dPairSnd => "dPairSnd"
