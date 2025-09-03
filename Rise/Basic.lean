import Lean.Data.Json

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
  | bvar (deBruijnIndex : Nat) (userName : Lean.Name)
  | mvar (id : Nat) (userName : Lean.Name)
  | nat  (n : Nat)
  | plus (n : RNat) (m : RNat)
  | minus (n : RNat) (m : RNat)
  | mult (n : RNat) (m : RNat)
  | pow (n : RNat) (m : RNat)
deriving Repr, BEq, DecidableEq


inductive RScalar
  | bool
  | int
  | i8
  | i16
  | i32
  | i64
  | u8
  | u16
  | u32
  | u64
  | f16
  | f32
  | f64

deriving Repr, BEq

-- DataType
--   δ ::= n.δ | δ × δ | "idx [" n "]" | scalar | n<scalar>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : Lean.Name)
  | mvar (id : Nat) (userName : Lean.Name)
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RScalar → RData
  | natType : RData
  | vector : RNat → RData → RData -- NOTE: second param should be scalar, but then we'd also need mvars for scalar, which is annoying, so i'll leave it as is for now.
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
  -- upi ->, pi -> fn
deriving Repr, BEq


def typeOfKind: RKind -> Type
  | .nat => RNat
  | .data => RData
  | .type => RType

mutual
structure TypedRExpr where
  node: TypedRExprNode
  type: RType
deriving Repr, BEq

inductive scalarlit
  | bool (x: Bool)

inductive TypedRExprNode where
  | bvar (deBruijnIndex : Nat)
  | fvar (userName : Lean.Name) -- this is a problem when multiple idents have the same name?
  | mvar (userName : Lean.Name) -- this is a problem when multiple idents have the same name?
-- mvar
  | const (userName : Lean.Name)
  | lit (val : Nat) -- scalarlit
  | app (fn arg : TypedRExpr)
  -- depapp / dapp, fn: typedrexpr, kind: RKind, arg: typeOfKind kind

  -- (fun (dt : data) => ((fun (n : nat) => fun (x : n.dt) => x) (42 : RNat))) (f32 : RData)

  | lam (binderName : Lean.Name) (binderType : RType) (body : TypedRExpr)
  | ulam (binderName : Lean.Name) (binderKind : RKind) (body : TypedRExpr)
  -- deplam / dlam
deriving Repr, BEq
end

-- abbrev MVCtxElem := Lean.Name × RKind × Option RType
-- abbrev MVCtx := Array MVCtxElem

abbrev KCtxElem := Lean.Name × RKind
abbrev KCtx := Array KCtxElem

abbrev TCtxElem := Lean.Name × RType
abbrev TCtx := Array TCtxElem

structure MetaVarDeclaration where
  userName : Lean.Name := Lean.Name.anonymous
  kind : RKind
  type : Option RType := none

abbrev RMVarId := Nat
abbrev RBVarId := Nat

inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)
deriving BEq

abbrev Substitution := List (RMVarId × SubstEnum)



def RNat.substNat (t : RNat) (x : RMVarId) (s : RNat) : RNat :=
    match t with
    | .mvar y _ => if x == y then s else t
    | .bvar .. => t
    | .nat _ => t
    | .plus n m => .plus (n.substNat x s) (m.substNat x s)
    | .minus n m => .minus (n.substNat x s) (m.substNat x s)
    | .mult n m => .mult (n.substNat x s) (m.substNat x s)
    | .pow n m => .pow (n.substNat x s) (m.substNat x s)

def RNat.subst (t : RNat) (x : RMVarId) (s : SubstEnum) : RNat :=
  match s with
  | .data _ => t
  | .nat s => t.substNat x s

def RData.substNat (t : RData) (x : RMVarId) (s : RNat) : RData :=
  match t with
  | .array k d => .array (k.substNat x s) (d.substNat x s)
  | .pair l r => .pair (l.substNat x s) (r.substNat x s)
  | .index k => .index (k.substNat x s)
  | .vector k d => .vector (k.substNat x s) (d.substNat x s)
  | .mvar .. | .bvar .. | .scalar .. | .natType => t

def RData.substData (t : RData) (x : RMVarId) (s : RData) : RData :=
  match t with
  | .mvar y _ => if x == y then s else t
  | .array k d => .array k (d.substData x s)
  | .pair l r => .pair (l.substData x s) (r.substData x s)
  | .vector k d => .vector k (d.substData x s)
  | .index .. | .bvar .. | .scalar .. | .natType => t

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
  | .plus n m => n.has v || m.has v
  | .minus n m => n.has v || m.has v
  | .mult n m => n.has v || m.has v
  | .pow n m => n.has v || m.has v

def RData.has (v : RMVarId) : RData → Bool
  | .mvar id _ => id == v
  | .array _ d => d.has v
  | .pair l r => l.has v || r.has v
  | .vector _ d => d.has v
  | .bvar .. | .index .. | .scalar .. | .natType => false

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

def digitToSubscript (d : Nat) : Char :=
  match d with
  | 0 => '₀'
  | 1 => '₁'
  | 2 => '₂'
  | 3 => '₃'
  | 4 => '₄'
  | 5 => '₅'
  | 6 => '₆'
  | 7 => '₇'
  | 8 => '₈'
  | 9 => '₉'
  | _ => '₀' -- :/

def natToSubscript (n : Nat) : String :=
  let rec getDigits (n : Nat) : List Nat :=
    if n < 10 then [n]
    else (n % 10) :: getDigits (n / 10)
  let digits := getDigits n
  String.mk (digits.reverse.map digitToSubscript)



instance : ToString RKind where
  toString
    | RKind.nat => "nat"
    | RKind.data => "data"
    | RKind.type => "type"

instance : ToString RNat where
  toString :=
    let rec go : RNat → String
      | .bvar idx name => s!"{name}@{idx}"
      | .mvar id name => s!"?{name}{natToSubscript id}"
      | .nat n => s!"{n}"
      | .plus n m => s!"({go n}+{go m})"
      | .minus n m => s!"({go n}-{go m})"
      | .mult n m => s!"({go n}*{go m})"
      | .pow n m => s!"({go n}^{go m})"
    go

def RData.toString : RData → String
  | .bvar idx name => s!"{name}@{idx}"
  | .mvar id name => s!"?{name}{natToSubscript id}"
  | .array n d => s!"{n}·{d.toString}"
  | .pair d1 d2 => s!"({d1.toString} × {d2.toString})"
  | .index n => s!"idx[{n}]"
  | .scalar x => repr x |>.pretty
  | .natType => "natType"
  | .vector n d => s!"{n}<{d.toString}>"

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
  | RType.pi binderType body =>
    match binderType with
    | .pi .. | .upi .. => s!"({RType.toString binderType}) → {RType.toString body}"
    | _ => s!"{RType.toString binderType} → {RType.toString body}"

instance : ToString RType where
  toString := RType.toString


instance : ToString SubstEnum where
  toString
    | SubstEnum.data rdata => s!"data({rdata})"
    | SubstEnum.nat rnat => s!"nat({rnat})"

instance : ToString Substitution where
  toString s := String.intercalate "\n" (s.map toString)

-- def TypedRExpr.toString : TypedRExpr → String
--   | bvar id => s!"@{id}"
--   | fvar s => s.toString
--   | const s => s.toString
--   | lit n => s!"{n}"
--   | app f e => s!"({f.toString} {e.toString})"
--   | lam s t b => match t with
--     | some t => s!"(λ {s} : {t} => {b.toString})"
--     | none => s!"(λ {s} => {b.toString})"
--   | ulam s k b => match k with
--     | some k => s!"(Λ {s} : {k} => {b.toString})"
--     | none => s!"(Λ {s} => {b.toString})"

-- instance : ToString TypedRExpr where
--   toString := TypedRExpr.toString

partial def TypedRExprNode.render : TypedRExprNode → Std.Format
  | bvar id => f!"@{id}"
  | mvar id => f!"?{id}"
  | fvar s => s.toString
  | const s => s.toString
  | lit n => s!"{n}"
  | app f e => match f.node, e.node with
    | app .. , app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | app .. , _      => f.node.render ++ " " ++ e.node.render
    | _      , app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | _,_ => f.node.render ++ " " ++ e.node.render
  | lam s t b => Std.Format.paren s!"λ {s} : {t} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | ulam s k b => Std.Format.paren s!"Λ {s} : {k} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line

partial def TypedRExprNode.renderInline : TypedRExprNode → Std.Format
  | bvar id => f!"@{id}"
  | mvar id => f!"?{id}"
  | fvar s => s.toString
  | const s => s.toString
  | lit n => s!"{n}"
  | app f e => match f.node, e.node with
    | app .. , app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | app .. , _      => f.node.renderInline ++ " " ++ e.node.renderInline
    | _      , app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | _,_ => f.node.renderInline ++ " " ++ e.node.renderInline
  | lam s t b => Std.Format.paren s!"λ {s} : {t} => {b.node.renderInline}"
  | ulam s k b => Std.Format.paren s!"Λ {s} : {k} => {b.node.renderInline}"

instance : Std.ToFormat TypedRExprNode where
  format := TypedRExprNode.render

instance : ToString TypedRExprNode where
  toString e := Std.Format.pretty e.render

private
def indent (s : String) : String :=
  s.trim |>.splitOn "\n" |>.map (λ s => "  " ++ s) |> String.intercalate "\n"


instance : ToString TypedRExpr where
  toString e := "expr:\n" ++ (indent <| toString e.node) ++ "\ntype:\n" ++ (indent <| toString e.type)

open Lean in
partial def TypedRExpr.toJson (e : TypedRExpr) : Json :=
  match e.node with
  | .app e1 e2 => let children := Json.arr <| #[e1, e2].map toJson
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", children)]
  | .lam un _ b =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", Json.arr #[toJson b])]
  | .ulam un _ b =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", Json.arr #[toJson b])]
  | _ =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type)]

instance : Lean.ToJson TypedRExpr where
  toJson e := e.toJson
