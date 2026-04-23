import C.Basic

structure Environment where
    identEnv: Std.HashMap Lean.Name CExpr
    commEnv: Std.HashMap Lean.Name CStmt
    letNatEnv: Std.HashMap Lean.Name DPIAPhrase -- no where used

def mkEnv (identEnv: Std.HashMap Lean.Name CExpr) (commEnv: Std.HashMap Lean.Name CStmt) (letNatEnv: Std.HashMap Lean.Name DPIAPhrase) : Environment :=
    {identEnv := identEnv, commEnv := commEnv, letNatEnv := letNatEnv : Environment}

def updatedIdentEnv (e : Environment) (kv : Lean.Name) (n : Nat) (c : CExpr) : Environment :=
    {identEnv := e.identEnv.insert kv c
     commEnv := e.commEnv
     letNatEnv := e.letNatEnv}

def lookUpIdentEnv (e: Environment) (kv : Lean.Name) (n : Nat) : CExpr :=
    match e.identEnv.get? kv with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"

def updatedCommEnv (e : Environment) (kv : Lean.Name) (n : Nat) (c : CStmt) : Environment :=
    {identEnv := e.identEnv
     commEnv := e.commEnv.insert kv c
     letNatEnv := e.letNatEnv}

def lookUpCommEnv  (e: Environment) (kv : Lean.Name) (n : Nat) : CStmt :=
    match e.commEnv.get? kv with
        | some y => y
        | none => panic! s!"expected to find {kv}@{n} in environment"


def updatedNatEnv (e : Environment) (kv : Lean.Name) (n : Nat) (p : DPIAPhrase) : Environment :=
    {identEnv := e.identEnv
     commEnv := e.commEnv
     letNatEnv := e.letNatEnv.insert kv p}

def lookUpNatEnv  (e: Environment) (kv : Lean.Name) (n : Nat) : DPIAPhrase :=
    match e.letNatEnv.get? kv with
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
