import Lean.Data.Json
import Lean.Elab

open Lean.Name
abbrev Name := Lean.Name
--
-- Kind
--   κ ::= nat | data (Natural Number Kind, Datatype Kind)
inductive RKind
  | nat
  | data
  | type
  | nat2nat
  | nat2data
  | addrSpace
deriving BEq, Hashable, Repr

-- Nat
--   n ::= 0 | n + n | n · n | ... (Natural Number Literals, Binary Operations)
inductive RNat
  | bvar (deBruijnIndex : Nat) (userName : Name)
  | mvar (id : Nat) (userName : Name)
  | nat  (n : Nat)
  | plus (n : RNat) (m : RNat)
  | minus (n : RNat) (m : RNat)
  | mult (n : RNat) (m : RNat)
  | div (n : RNat) (m : RNat)
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
  | float
  | f16
  | f32
  | f64
deriving Repr, BEq

-- DataType
--   δ ::= n.δ | δ × δ | "idx [" n "]" | scalar | n<scalar>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : Name)
  | mvar (id : Nat) (userName : Name)
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RScalar → RData
  | natType : RData
  | vector : RNat → RData → RData -- NOTE: second param should be scalar, but then we'd also need mvars for scalar, which is annoying, so i'll leave it as is for now.
deriving Repr, BEq

-- Im-/ex-plicity of parameters
inductive RBinderInfo
  | explicit
  | implicit
deriving Repr, BEq

-- Types
--   τ ::= δ | τ → τ | (x : κ) → τ (Data Type, Function Type, Dependent Function Type)
inductive RType
  | data (dt : RData)
  | pi (binderKind : RKind) (binderInfo : RBinderInfo) (userName : Name) (body : RType)
  | fn (binderType : RType) (body : RType)
deriving Repr, BEq

inductive RAddrSpace
  | global
  | local
  | «private»
  | constant
deriving Repr, BEq

inductive RWrapper
  | nat (v: RNat)
  | data (v: RData)
  | nat2nat (binderName : Name) (body : RNat)
  | nat2data (binderName : Name) (body : RData)
  | addrSpace (val : RAddrSpace)
deriving Repr, BEq

inductive RLit
  | bool (val : Bool)
  | float (val : String) -- TODO: better representation
  | int (val : Int)
deriving Repr, BEq

mutual
structure TypedRExpr where
  node: TypedRExprNode
  type: RType
deriving Repr, BEq

inductive TypedRExprNode
  | bvar (deBruijnIndex : Nat) (userName: Name)
  | const (userName : Name)
  | lit (val : RLit)
  | app (fn arg : TypedRExpr)
  | depapp (fn : TypedRExpr) (arg : RWrapper)
  | lam (binderName : Name) (binderType : RType) (body : TypedRExpr)
  | deplam (binderName : Name) (binderKind : RKind) (body : TypedRExpr)
deriving Repr, BEq
end

abbrev KindingContextElement := Name × RKind
abbrev KindingContext := Array KindingContextElement

abbrev TypingContextElement := Name × RType
abbrev TypingContext := Array TypingContextElement

structure MetaVarDeclaration where
  userName : Name := .anonymous
  kind : RKind
  type : Option RType := none

abbrev RMVarId := Nat
abbrev RBVarId := Nat

inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)
deriving BEq, Repr

abbrev Substitution := List (RMVarId × SubstEnum)

def RNat.substNat (t : RNat) (x : RMVarId) (s : RNat) : RNat :=
    match t with
    | .mvar y _ => if x == y then s else t
    | .bvar .. => t
    | .nat _ => t
    | .plus n m => .plus (n.substNat x s) (m.substNat x s)
    | .minus n m => .minus (n.substNat x s) (m.substNat x s)
    | .mult n m => .mult (n.substNat x s) (m.substNat x s)
    | .div n m => .div (n.substNat x s) (m.substNat x s)
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
  | .pi bk pc un body => .pi bk pc un (body.substNat x s)
  | .fn binderType body => .fn (binderType.substNat x s) (body.substNat x s)

def RType.substData (t : RType) (x : RMVarId) (s : RData) : RType :=
  match t with
  | .data dt => .data (dt.substData x s)
  | .pi bk pc un body => .pi bk pc un (body.substData x s)
  | .fn binderType body => .fn (binderType.substData x s) (body.substData x s)

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
  | .div n m => n.has v || m.has v
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

def SubstEnum.apply (se : SubstEnum) (subst : Substitution) : SubstEnum :=
  match se with
  | .data s => data <| subst.foldr (fun (id, replacement) acc => acc.subst id replacement) s
  | .nat s => nat <| subst.foldr (fun (id, replacement) acc => acc.subst id replacement) s

instance : ToString RKind where
  toString
    | .nat => "nat"
    | .data => "data"
    | .type => "type"
    | .nat2nat => "nat2nat"
    | .nat2data => "nat2data"
    | .addrSpace => "addrSpace"

instance : ToString RNat where
  toString :=
    let rec go : RNat → String
      | .bvar idx name => s!"{name}@{idx}"
      | .mvar id name => s!"{name}?{id}"
      | .nat n => s!"{n}"
      | .plus n m => s!"({go n}+{go m})"
      | .minus n m => s!"({go n}-{go m})"
      | .mult n m => s!"({go n}*{go m})"
      | .div n m => s!"({go n}/{go m})"
      | .pow n m => s!"({go n}^{go m})"
    go

instance : ToString RLit where
  toString
    | .bool b => s!"{b}"
    | .int i => s!"{i}"
    | .float f => s!"{f}"


instance : ToString RScalar where
  toString
    | .bool => "bool"
    | .int  => "int"
    | .i8   => "i8"
    | .i16  => "i16"
    | .i32  => "i32"
    | .i64  => "i64"
    | .u8   => "u8"
    | .u16  => "u16"
    | .u32  => "u32"
    | .u64  => "u64"
    | .float => "float"
    | .f16  => "f16"
    | .f32  => "f32"
    | .f64  => "f64"

def RData.toString : RData → String
  | .bvar idx name => s!"{name}@{idx}"
  | .mvar id name  => s!"{name}?{id}"
  | .array n d     => s!"{n}·{d.toString}"
  | .pair d1 d2    => s!"({d1.toString} × {d2.toString})"
  | .index n       => s!"idx[{n}]"
  | .scalar x      => s!"{x}"
  | .natType       => "natType"
  | .vector n d    => s!"{n}<{d.toString}>"

instance : ToString RData where
  toString := RData.toString

instance : ToString RBinderInfo where
  toString
    | RBinderInfo.explicit => "explicit"
    | RBinderInfo.implicit => "implicit"

def RType.toString : RType → String
  | RType.data dt => RData.toString dt
  | RType.pi kind pc un body =>
      let plicityStr := if pc == RBinderInfo.implicit then "{" else "("
      let plicityEnd := if pc == RBinderInfo.implicit then "}" else ")"
      s!"{plicityStr}{un} : {kind}{plicityEnd} → {RType.toString body}"
  | RType.fn binderType body =>
    match binderType with
    | .fn .. | .pi .. => s!"({RType.toString binderType}) → {RType.toString body}"
    | _ => s!"{RType.toString binderType} → {RType.toString body}"

instance : ToString RType where
  toString := RType.toString


instance : ToString SubstEnum where
  toString
    | SubstEnum.data rdata => s!"data({rdata})"
    | SubstEnum.nat rnat => s!"nat({rnat})"

instance : ToString Substitution where
  toString s := String.intercalate "\n" (s.map toString)

def RWrapper.render : RWrapper -> Std.Format
  | .nat v => toString v ++ " : nat"
  | .data v => toString v ++ " : data"
  | .nat2nat bn b => s!"{bn} ↦ {b} : nat2nat"
  | .nat2data bn b => s!"{bn} ↦ {b} : nat2data"
  | .addrSpace a => repr a
  -- | .type v => toString v ++ " : type"

partial def TypedRExprNode.render : TypedRExprNode → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .const s      => s.toString
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | .app .. , _       => f.node.render ++ " " ++ e.node.render
    | _       , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | _       , _       => f.node.render ++ " " ++ e.node.render
  | .depapp f e   => f.node.render ++ " " ++ Std.Format.paren e.render
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line

partial def TypedRExprNode.renderInline : TypedRExprNode → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .const s      => s.toString
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | .app .. , _       => f.node.renderInline ++ " " ++ e.node.renderInline
    | _       , .app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | _       ,       _ => f.node.renderInline ++ " " ++ e.node.renderInline
  | .depapp f e   => f.node.renderInline ++ " " ++ Std.Format.paren e.render
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} => {b.node.renderInline}"
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} => {b.node.renderInline}"

instance : Std.ToFormat TypedRExprNode where
  format := TypedRExprNode.render

instance : ToString TypedRExprNode where
  toString e := Std.Format.pretty e.render

private def indent (s : String) : String :=
  s.trim |>.splitOn "\n" |>.map (λ s => "  " ++ s) |> String.intercalate "\n"

instance : ToString TypedRExpr where
  toString e := "expr:\n" ++ (indent <| toString e.node) ++ "\ntype:\n" ++ (indent <| toString e.type)

open Lean in
partial def TypedRExpr.toJson (e : TypedRExpr) : Json :=
  match e.node with
  | .app e1 e2 => let children := Json.arr <| #[e1, e2].map toJson
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", children)]
  | .lam _ _ b =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", Json.arr #[toJson b])]
  | .deplam _ _ b =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type), ("children", Json.arr #[toJson b])]
  | _ =>
    Json.mkObj [("expr", e.node.renderInline.pretty), ("type", toString e.type)]

instance : Lean.ToJson TypedRExpr where
  toJson e := e.toJson

register_option egg.debug_enable : Bool := {
  defValue := false
  group := "egg"
  descr := "Enables running egg and comparing results to sympy."
}

/-- Command for pretty printing using the ToString instance. -/
syntax "#pp " term : command
macro_rules
| `(#pp $e) => `(#eval IO.print <| toString $e)
