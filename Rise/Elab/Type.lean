import Lean
import Rise.Basic
import Rise.Elab.RElabM
open Lean Elab Meta Command

declare_syntax_cat rise_kind
syntax "nat"                   : rise_kind
syntax "data"                  : rise_kind
syntax "nat2nat"                  : rise_kind
syntax "nat2data"                  : rise_kind
syntax "addrSpace"                  : rise_kind

syntax "[RiseK|" rise_kind "]" : term

macro_rules
  | `([RiseK| nat]) => `(RKind.nat)
  | `([RiseK| data]) => `(RKind.data)

partial def elabToRKind : Syntax -> RElabM RKind
  | `(rise_kind| nat) => return RKind.nat
  | `(rise_kind| data) => return RKind.data
  | `(rise_kind| nat2nat) => return RKind.nat2nat
  | `(rise_kind| nat2data) => return RKind.nat2data
  | `(rise_kind| addrSpace) => return RKind.addrSpace
  | _ => throwUnsupportedSyntax

instance : ToExpr RAddrSpace where
  toExpr e := match e with
  | .global => mkConst ``RAddrSpace.global
  | .local => mkConst ``RAddrSpace.local
  | .private => mkConst ``RAddrSpace.private
  | .constant => mkConst ``RAddrSpace.constant
  toTypeExpr := mkConst ``RAddrSpace

instance : ToExpr RKind where
  toExpr e := match e with
  | .nat => mkConst ``RKind.nat
  | .data => mkConst ``RKind.data
  | .type => mkConst ``RKind.type
  | .nat2nat => mkConst ``RKind.nat2nat
  | .nat2data => mkConst ``RKind.nat2data
  | .addrSpace => mkConst ``RKind.addrSpace
  toTypeExpr := mkConst ``RKind

declare_syntax_cat rise_nat
syntax    num                          : rise_nat
syntax    ident                        : rise_nat
syntax:10 rise_nat:10 "+" rise_nat:11  : rise_nat
syntax:10 rise_nat:10 "-" rise_nat:11  : rise_nat
syntax:20 rise_nat:20 "*" rise_nat:21  : rise_nat
syntax:20 rise_nat:20 "/" rise_nat:21  : rise_nat
syntax:30 rise_nat    "^" rise_nat     : rise_nat
syntax    "(" rise_nat ")"             : rise_nat

syntax "[RiseN|" rise_nat "]" : term

partial def elabToRNat : Syntax → RElabM RNat
  | `(rise_nat| $n:num) =>
    return RNat.nat n.getNat

  | `(rise_nat| $x:ident) => do
    let kctx ← getKCtx
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some idx =>
      return RNat.bvar idx x.getId
    | none => throwErrorAt x s!"rnat: unknown identifier {mkConst x.getId}"

  | `(rise_nat| $n:rise_nat + $m:rise_nat) => do
    let n ← elabToRNat n
    let m ← elabToRNat m
    return RNat.plus n m

  | `(rise_nat| $n:rise_nat - $m:rise_nat) => do
    let n ← elabToRNat n
    let m ← elabToRNat m
    return RNat.minus n m

  | `(rise_nat| $n:rise_nat * $m:rise_nat) => do
    let n ← elabToRNat n
    let m ← elabToRNat m
    return RNat.mult n m

  | `(rise_nat| $n:rise_nat / $m:rise_nat) => do
    let n ← elabToRNat n
    let m ← elabToRNat m
    return RNat.div n m

  | `(rise_nat| $n:rise_nat ^ $m:rise_nat) => do
    let n ← elabToRNat n
    let m ← elabToRNat m
    return RNat.pow n m

  | `(rise_nat| ($n:rise_nat)) => do
    elabToRNat n

  | _ => throwUnsupportedSyntax

instance : ToExpr RNat where
  toExpr :=
    let rec go : RNat → Expr
    | RNat.bvar deBruijnIndex userName =>
      let f := mkConst ``RNat.bvar
      mkAppN f #[mkNatLit deBruijnIndex, toExpr userName]
    | RNat.mvar id userName =>
      let f := mkConst ``RNat.mvar
      mkAppN f #[mkNatLit id, toExpr userName]
    | RNat.nat n =>
      let f := mkConst ``RNat.nat
      mkAppN f #[mkNatLit n]
    | .plus n m =>
      let f := mkConst ``RNat.plus
      mkAppN f #[go n, go m]
    | .minus n m =>
      let f := mkConst ``RNat.minus
      mkAppN f #[go n, go m]
    | .mult n m =>
      let f := mkConst ``RNat.mult
      mkAppN f #[go n, go m]
    | .div n m =>
      let f := mkConst ``RNat.div
      mkAppN f #[go n, go m]
    | .pow n m =>
      let f := mkConst ``RNat.pow
      mkAppN f #[go n, go m]
    go
  toTypeExpr := mkConst ``RNat

partial def elabRNat : Syntax → RElabM Expr
  | stx => do
    let n ← elabToRNat stx
    return toExpr n


declare_syntax_cat rise_data
syntax:50 rise_nat "·" rise_data:50  : rise_data
syntax:10 rise_data "×" rise_data    : rise_data
syntax    ident                      : rise_data
syntax    "idx[" rise_nat "]"        : rise_data
syntax    rise_nat "<" rise_data ">" : rise_data
syntax    "(" rise_data ")"          : rise_data
syntax    "natType"                  : rise_data
syntax    "bool"                     : rise_data
syntax    "int"                      : rise_data
syntax    "i8"                       : rise_data
syntax    "i16"                      : rise_data
syntax    "i32"                      : rise_data
syntax    "i64"                      : rise_data
syntax    "u8"                       : rise_data
syntax    "u16"                      : rise_data
syntax    "u32"                      : rise_data
syntax    "u64"                      : rise_data
syntax    "f16"                      : rise_data
syntax    "f32"                      : rise_data
syntax    "f64"                      : rise_data


partial def elabToRData : Syntax → RElabM RData
  | `(rise_data| bool) => return RData.scalar .bool
  | `(rise_data|  int) => return RData.scalar .int
  | `(rise_data|   i8) => return RData.scalar .i8
  | `(rise_data|  i16) => return RData.scalar .i16
  | `(rise_data|  i32) => return RData.scalar .i32
  | `(rise_data|  i64) => return RData.scalar .i64
  | `(rise_data|   u8) => return RData.scalar .u8
  | `(rise_data|  u16) => return RData.scalar .u16
  | `(rise_data|  u32) => return RData.scalar .u32
  | `(rise_data|  u64) => return RData.scalar .u64
  | `(rise_data|  f16) => return RData.scalar .f16
  | `(rise_data|  f32) => return RData.scalar .f32
  | `(rise_data|  f64) => return RData.scalar .f64

  | `(rise_data|  natType) => return RData.natType

  | `(rise_data| $x:ident) => do
    let kctx ← getKCtx
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some index =>
      return RData.bvar index x.getId
    | none => throwErrorAt x s!"rdata: unknown identifier {mkConst x.getId}"

  | `(rise_data| $n:rise_nat·$d:rise_data) => do
    let n ← elabToRNat n
    let d ← elabToRData d
    return RData.array n d

  | `(rise_data| $l:rise_data × $r:rise_data) => do
    let l ← elabToRData l
    let r ← elabToRData r
    return RData.pair l r

  | `(rise_data| idx[$n:rise_nat]) => do
    let n <- elabToRNat n
    return RData.index n

  | `(rise_data| $n:rise_nat < $d:rise_data >) => do
    let n <- elabToRNat n
    let d <- elabToRData d
    return RData.vector n d

  | `(rise_data| ($d:rise_data)) =>
    elabToRData d


  | _ => throwUnsupportedSyntax

instance : ToExpr RData where
  toExpr :=
    let rec go : RData → Expr
    | RData.natType => mkConst ``RData.natType
    | RData.scalar x =>
        let c := mkConst ``RData.scalar
        let v := match x with
        | .bool => mkConst ``RScalar.bool
        | .int  => mkConst ``RScalar.int
        | .i8   => mkConst ``RScalar.i8
        | .i16  => mkConst ``RScalar.i16
        | .i32  => mkConst ``RScalar.i32
        | .i64  => mkConst ``RScalar.i64
        | .u8   => mkConst ``RScalar.u8
        | .u16  => mkConst ``RScalar.u16
        | .u32  => mkConst ``RScalar.u32
        | .u64  => mkConst ``RScalar.u64
        | .float  => mkConst ``RScalar.float
        | .f16  => mkConst ``RScalar.f16
        | .f32  => mkConst ``RScalar.f32
        | .f64  => mkConst ``RScalar.f64
        mkAppN c #[v]
    | RData.bvar deBruijnIndex userName =>
      mkAppN (mkConst ``RData.bvar) #[mkNatLit deBruijnIndex, toExpr userName]
    | RData.mvar id userName =>
      mkAppN (mkConst ``RData.mvar) #[mkNatLit id, toExpr userName]
    | RData.array n d =>
      mkAppN (mkConst ``RData.array) #[toExpr n, go d]
    | RData.pair l r =>
      mkAppN (mkConst ``RData.pair) #[go l, go r]
    | RData.index n =>
      mkAppN (mkConst ``RData.index) #[toExpr n]
    | RData.vector n d =>
      mkAppN (mkConst ``RData.vector) #[toExpr n, go d]
    go
  toTypeExpr := mkConst ``RData

partial def elabRData : Syntax → RElabM Expr
  | stx => do
    let d ← elabToRData stx
    return toExpr d

instance : ToExpr RBinderInfo where
  toExpr e := match e with
  | RBinderInfo.explicit => mkConst ``RBinderInfo.explicit
  | RBinderInfo.implicit => mkConst ``RBinderInfo.implicit
  toTypeExpr := mkConst ``RBinderInfo

declare_syntax_cat rise_type
syntax rise_data                                  : rise_type
syntax rise_type "→" rise_type                    : rise_type
syntax "(" rise_type ")"                          : rise_type
syntax "{" ident+ ":" rise_kind "}" "→" rise_type : rise_type
syntax "(" ident+ ":" rise_kind ")" "→" rise_type  : rise_type

macro_rules
  | `(rise_type| {$x:ident $y:ident $xs:ident* : $k:rise_kind} → $t:rise_type) =>
    match xs with
    | #[] =>
      `(rise_type| {$x : $k} → {$y : $k} → $t)
    | _ =>
      `(rise_type| {$x : $k} → {$y : $k} → {$xs* : $k} → $t)

  | `(rise_type| ($x:ident $y:ident $xs:ident* : $k:rise_kind) → $t:rise_type) =>
    match xs with
    | #[] =>
      `(rise_type| ($x : $k) → ($y : $k) → $t)
    | _ =>
      `(rise_type| ($x : $k) → ($y : $k) → ($xs* : $k) → $t)

partial def elabToRType : Syntax → RElabM RType
  | `(rise_type| $d:rise_data) => do
    let d ← elabToRData d
    return RType.data d

  | `(rise_type| ($d:rise_data)) => do
    let d ← elabToRData d
    return RType.data d

  | `(rise_type| $l:rise_type → $r:rise_type) => do
    let t ← elabToRType l
    let body ← elabToRType r
    return RType.fn t body

  | `(rise_type| ($t:rise_type)) => do
    elabToRType t

  | `(rise_type| {$x:ident : $k:rise_kind} → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← withNewType (x.getId, k) do elabToRType t
    return RType.pi k RBinderInfo.implicit x.getId body

  | `(rise_type| ($x:ident : $k:rise_kind) → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← withNewType (x.getId, k) do elabToRType t
    return RType.pi k RBinderInfo.explicit x.getId body
  | _ => throwUnsupportedSyntax

instance : ToExpr RType where
  toExpr :=
    let rec go : RType → Expr
    | RType.data d =>
      let f := mkConst ``RType.data
      mkAppN f #[toExpr d]
    | RType.pi binderKind pc userName body =>
      let f := mkConst ``RType.pi
      mkAppN f #[toExpr binderKind, toExpr pc, toExpr userName, go body]
    | RType.fn binderType body =>
      let f := mkConst ``RType.fn
      mkAppN f #[go binderType, go body]
    go
  toTypeExpr := mkConst ``RType


partial def elabRType : Syntax → RElabM Expr
  | stx => do
    let t ← elabToRType stx
    return toExpr t

elab "[RiseT|" t:rise_type "]" : term => do
  -- macros run before elab, but we still have to manually expand macros
  let t ← liftMacroM <| expandMacros t
  let term ← liftToTermElabM <| elabRType t
  return term

private def RNat.supplyMVar (rn : RNat) (n : RBVarId) (m : RMVarId) : RNat :=
  match rn with
  | .bvar bn un => if bn == n then .mvar m un
    else if bn > n then
    .bvar (bn-1) un
    else rn
  | .mvar .. => rn
  | .nat .. => rn
  | .plus p q => .plus (p.supplyMVar n m) (q.supplyMVar n m)
  | .minus p q => .minus (p.supplyMVar n m) (q.supplyMVar n m)
  | .mult p q => .mult (p.supplyMVar n m) (q.supplyMVar n m)
  | .div p q => .div (p.supplyMVar n m) (q.supplyMVar n m)
  | .pow p q => .pow (p.supplyMVar n m) (q.supplyMVar n m)

private def RData.supplyMVar (dt : RData) (n : RBVarId) (m : RMVarId) : RData :=
  match dt with
  | .bvar bn un => if bn == n then .mvar m un else dt
  | .array rn dt => .array (rn.supplyMVar n m) (dt.supplyMVar n m)
  | .pair dt1 dt2 => .pair (dt1.supplyMVar n m) (dt2.supplyMVar n m)
  | .index rn => .index (rn.supplyMVar n m)
  | .vector rn d => .vector (rn.supplyMVar n m) (d.supplyMVar n m)
  | .mvar .. | .scalar .. | .natType => dt

/-- Substitutes outermost bvar (current de-bruijn index 0) with mvar of id mid. -/
def RType.supplyMVar (t : RType) (mid : RMVarId) : RType :=
  go t 0 mid where
  go : RType → RBVarId → RMVarId → RType
  | .data dt, n, m => .data (dt.supplyMVar n m)
  | .pi bk pc un b, n, m => .pi bk pc un (go b (n+1) m)
  | .fn bt b, n, m => .fn (go bt n m) (go b n m)

private def RNat.shiftBVars (rn : RNat) (n : Nat) : RNat :=
  match rn with
  | .bvar bn un => .bvar (bn + n) un
  | .mvar .. => rn
  | .nat .. => rn
  | .plus p q => .plus (p.shiftBVars n) (q.shiftBVars n)
  | .minus p q => .minus (p.shiftBVars n) (q.shiftBVars n)
  | .mult p q => .mult (p.shiftBVars n) (q.shiftBVars n)
  | .div p q => .div (p.shiftBVars n) (q.shiftBVars n)
  | .pow p q => .pow (p.shiftBVars n) (q.shiftBVars n)

private def RNat.supplyRNat (rn : RNat) (n : RBVarId) (rnat : RNat) : RNat :=
  match rn with
  | .bvar bn un => if bn == n then rnat.shiftBVars n
    else if bn > n then
    .bvar (bn-1) un
    else rn
  | .mvar .. => rn
  | .nat .. => rn
  | .plus p q => .plus (p.supplyRNat n rnat) (q.supplyRNat n rnat)
  | .minus p q => .minus (p.supplyRNat n rnat) (q.supplyRNat n rnat)
  | .mult p q => .mult (p.supplyRNat n rnat) (q.supplyRNat n rnat)
  | .div p q => .div (p.supplyRNat n rnat) (q.supplyRNat n rnat)
  | .pow p q => .pow (p.supplyRNat n rnat) (q.supplyRNat n rnat)

private def RData.supplyRNat (dt : RData) (n : RBVarId) (rnat : RNat) : RData :=
  match dt with
  | .array rn dt => .array (rn.supplyRNat n rnat) (dt.supplyRNat n rnat)
  | .pair dt1 dt2 => .pair (dt1.supplyRNat n rnat) (dt2.supplyRNat n rnat)
  | .index rn => .index (rn.supplyRNat n rnat)
  | .vector rn d => .vector (rn.supplyRNat n rnat) (d.supplyRNat n rnat)
  | .scalar .. | .bvar .. | .mvar .. | .natType => dt

/-- Supplies rnat to t, i.e. substitutes outermost bvar (current de-bruijn index 0) with rnat. -/
def RType.supplyRNat (t : RType) (rnat : RNat) : RType :=
  go t 0 rnat where
  go : RType → RBVarId → RNat → RType
  | .data dt, n, rnat => .data (dt.supplyRNat n rnat)
  | .pi bk pc un b, n, rnat => .pi bk pc un (go b (n+1) rnat)
  | .fn bt b, n, rnat => .fn (go bt n rnat) (go b n rnat)

private def RData.shiftBVars (rdata : RData) (n : Nat) : RData :=
  match rdata with
  | .bvar bn un => .bvar (bn + n) un
  | .scalar .. | .mvar .. | .natType => rdata
  | .array rn dt => .array rn (dt.shiftBVars n)
  | .pair dt1 dt2 => .pair (dt1.shiftBVars n) (dt2.shiftBVars n)
  | .index rn => .index rn
  | .vector rn dt => .vector rn (dt.shiftBVars n)

private def RData.supplyRData (dt : RData) (n : RBVarId) (rdata : RData) : RData :=
  match dt with
  | .bvar bn un => if bn == n then rdata.shiftBVars n
    else if bn > n then
    .bvar (bn-1) un
    else dt
  | .array rn dt => .array rn (dt.supplyRData n rdata)
  | .pair dt1 dt2 => .pair (dt1.supplyRData n rdata) (dt2.supplyRData n rdata)
  | .index rn => .index rn
  | .vector rn d => .vector rn (d.supplyRData n rdata)
  | .scalar .. | .mvar .. | .natType => dt

/-- Supplies rdata to t, i.e. substitutes outermost bvar (current de-bruijn index 0) with rdata. -/
def RType.supplyRData (t : RType) (rdata : RData) : RType :=
  go t 0 rdata where
  go : RType → RBVarId → RData → RType
  | .data dt, n, rdata => .data (dt.supplyRData n rdata)
  | .pi bk pc un b, n, rdata => .pi bk pc un (go b (n+1) rdata)
  | .fn bt b, n, rdata => .fn (go bt n rdata) (go b n rdata)

