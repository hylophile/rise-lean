
--
-- Kind
--   κ ::= nat | data (Natural Number Kind, Datatype Kind)
inductive RKind
  | nat
  | data
  | type
  -- | etc
deriving BEq, Hashable, Repr

-- Nat
--   n ::= 0 | n + n | n · n | ... (Natural Number Literals, Binary Operations)
inductive RNat
  | bvar (deBruijnIndex : Nat) (userName : String)
  | mvar (id : Nat) (userName : String)
  | nat: Nat → RNat
deriving Repr, BEq, DecidableEq

-- DataType
--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : Lean.Name)
  | mvar (id : Nat) (userName : Lean.Name)
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RData
  | vector : RNat → RData
deriving Repr, BEq

-- Im-/ex-plicity of parameters
inductive Plicity
  | ex
  | im
deriving Repr, BEq

-- Types
--   τ ::= δ | τ → τ | (x : κ) → τ (Data Type, Function Type, Dependent Function Type)
inductive RType where
  | data (dt : RData)
  -- do we need this distinction? yes, but we could do these cases with universe level. would need a RType.sort variant though
  | upi (binderKind : RKind) (pc : Plicity) (userName : Lean.Name) (body : RType)
  | pi (binderType : RType) (body : RType)
deriving Repr, BEq


inductive RExpr where
  | bvar (deBruijnIndex : Nat)
  | fvar (userName : Lean.Name) -- this is a problem when multiple idents have the same name?
-- mvar
  | const (userName : Lean.Name)
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (binderName : Lean.Name) (binderType : Option RType) (body : RExpr)
  | ulam (binderName : Lean.Name) (binderKind : Option RKind) (body : RExpr)
deriving Repr

-- abbrev MVCtxElem := Lean.Name × RKind × Option RType
-- abbrev MVCtx := Array MVCtxElem

abbrev KCtxElem := Lean.Name × Option RKind
abbrev KCtx := Array KCtxElem

abbrev TCtxElem := Lean.Name × Option RType
abbrev TCtx := Array TCtxElem

structure MetaVarDeclaration where
  userName : Lean.Name := Lean.Name.anonymous
  kind : RKind
  type : Option RType := none

abbrev RMVarId := Nat
abbrev RBVarId := Nat

-- def f : RMVarId → Nat := (·)
-- def x : BVarId := 0
-- example : Nat := f x


inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)

abbrev Substitution := List (RMVarId × SubstEnum)



def RNat.substNat (t : RNat) (x : RMVarId) (s : RNat) : RNat :=
    match t with
    | .mvar y _ => if x == y then s else t
    | .bvar .. => t
    | .nat _ => t

def RNat.subst (t : RNat) (x : RMVarId) (s : SubstEnum) : RNat :=
  match s with
  | .data _ => t
  | .nat s => t.substNat x s

def RData.substNat (t : RData) (x : RMVarId) (s : RNat) : RData :=
  match t with
  | .mvar .. => t
  | .array k d => .array (k.substNat x s) d
  | .pair l r => .pair (l.substNat x s) (r.substNat x s)
  | .bvar id un => .bvar id un
  | .index k => .index (k.substNat x s)
  | .scalar => .scalar
  | .vector k => .vector (k.substNat x s)

def RData.substData (t : RData) (x : RMVarId) (s : RData) : RData :=
  match t with
  | .mvar y _ => if x == y then s else t
  | .array k d => .array k (d.substData x s)
  | .pair l r => .pair (l.substData x s) (r.substData x s)
  | .bvar id un => .bvar id un
  | .index k => .index k
  | .scalar => .scalar
  | .vector k => .vector k

def RData.subst (t : RData) (x : RMVarId) (s : SubstEnum) : RData :=
  match s with
  | .data s => t.substData x s
  | .nat s => t.substNat x s

def RType.substNat (t : RType) (x : RMVarId) (s : RNat) : RType :=
  match t with
  | .data dt => .data (dt.substNat x s)
  | .upi bk pc un body => .upi bk pc un (body.substNat x s)
  | .pi binderType body => .pi (binderType.substNat x s) (body.substNat x s)

def RType.substData (t : RType) (x : RMVarId) (s : RData) : RType :=
  match t with
  | .data dt => .data (dt.substData x s)
  | .upi bk pc un body => .upi bk pc un (body.substData x s)
  | .pi binderType body => .pi (binderType.substData x s) (body.substData x s)

def RType.subst (t : RType) (x : RMVarId) (s : SubstEnum) : RType :=
  match s with
  | .data s => t.substData x s
  | .nat s => t.substNat x s

def RNat.has (v : RMVarId) : RNat → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .nat _ => false

def RData.has (v : RMVarId) : RData → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .array _ d => d.has v
  | .pair l r => l.has v || r.has v
  | .index .. => false
  | .scalar => false
  | .vector .. => false

def RNat.apply (t : RNat) (subst : Substitution) : RNat :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

def RData.apply (t : RData) (subst : Substitution) : RData :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

def RType.apply (t : RType) (subst : Substitution) : RType :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t


------------------------------------------------
--
--
-- 

instance : ToString RKind where
  toString
    | RKind.nat => "nat"
    | RKind.data => "data"
    | RKind.type => "type"


instance : ToString RNat where
  toString
    | RNat.bvar idx name => s!"{name}@{idx}"
    | RNat.mvar id name => s!"?{name}_{id}"
    | RNat.nat n => s!"{n}"


def RData.toString : RData → String
  | RData.bvar idx name => s!"{name}@{idx}"
  | RData.mvar id name => s!"?{name}_{id}"
  | RData.array n d => s!"{n}.{RData.toString d}"
  | RData.pair d1 d2 => s!"({RData.toString d1} × {RData.toString d2})"
  | RData.index n => s!"idx[{n}]"
  | RData.scalar => "scalar"
  | RData.vector n => s!"{n}<float>"

instance : ToString RData where
  toString := RData.toString

instance : ToString Plicity where
  toString
    | Plicity.ex => "explicit"
    | Plicity.im => "implicit"

def RType.toString : RType → String
  | RType.data dt => RData.toString dt
  | RType.upi kind pc un body =>
      let plicityStr := if pc == Plicity.im then "{" else "("
      let plicityEnd := if pc == Plicity.im then "}" else ")"
      s!"{plicityStr}{un} : {kind}{plicityEnd} → {RType.toString body}"
  | RType.pi binderType body => s!"{RType.toString binderType} → {RType.toString body}"

instance : ToString RType where
  toString := RType.toString


instance : ToString SubstEnum where
  toString
    | SubstEnum.data rdata => s!"data({rdata})"
    | SubstEnum.nat rnat => s!"nat({rnat})"
    
instance : ToString Substitution where
  toString s := String.intercalate "\n" (s.map toString)
