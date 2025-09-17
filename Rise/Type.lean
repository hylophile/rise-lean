import Lean
import Rise.Basic
import Rise.RElabM
open Lean Elab Meta Command
open PrettyPrinter Delaborator SubExpr

-- abbrev MVarCtx := Array (Name × Expr)


declare_syntax_cat rise_kind
syntax "nat"                   : rise_kind
syntax "data"                  : rise_kind
syntax "[RiseK|" rise_kind "]" : term

macro_rules
  | `([RiseK| nat]) => `(RKind.nat)
  | `([RiseK| data]) => `(RKind.data)

partial def elabToRKind : Syntax -> RElabM RKind
  | `(rise_kind| nat ) => return RKind.nat
  | `(rise_kind| data ) => return RKind.data
  | _ => throwUnsupportedSyntax

instance : ToExpr RKind where
  toExpr e := match e with
  | RKind.nat => mkConst ``RKind.nat
  | RKind.data => mkConst ``RKind.data
  | RKind.type => mkConst ``RKind.type
  toTypeExpr := mkConst ``RKind


declare_syntax_cat rise_nat
syntax    num                          : rise_nat
syntax    ident                        : rise_nat
syntax:10 rise_nat:10 "+" rise_nat:11  : rise_nat
syntax:10 rise_nat:10 "-" rise_nat:11  : rise_nat
syntax:20 rise_nat:20 "*" rise_nat:21  : rise_nat
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
    -- | none =>
    --   let mctx ← getMVCtx
    --   match mctx.reverse.findIdx? (λ (name, _, _) => name == x.getId) with
    --   | some idx =>
    --     return RNat.mvar idx x.getId.toString
    --   | none => throwErrorAt x s!"rnat: unknown identifier {mkConst x.getId}"

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
    -- let mctx ← getMVCtx
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some index =>
      return RData.bvar index x.getId
    | none => throwErrorAt x s!"rdata: unknown identifier {mkConst x.getId}"

    -- | none =>
      -- match mctx.reverse.findIdx? (λ (name, _, _) => name == x.getId) with
      -- | some index =>
      --   return RData.mvar index x.getId.toString
      -- | none => throwErrorAt x s!"rdata: unknown identifier {mkConst x.getId}"

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

-- set_option pp.raw true
-- set_option pp.raw.maxDepth 10

-- i bet this could be written nicer
macro_rules
  | `(rise_type| {$x:ident $y:ident $xs:ident* : $k:rise_kind} → $t:rise_type) =>
    match xs with
    | #[] =>
      `(rise_type| {$x : $k} → {$y : $k} → $t)
    | _ =>
      `(rise_type| {$x : $k} → {$y : $k} → {$xs* : $k} → $t)

macro_rules
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
  -- macros run before elab, but we still have to manually expand macros?
  let t ← liftMacroM <| expandMacros t
  let term ← liftToTermElabM <| elabRType t
  return term


-- set_option pp.rawOnError true
-- @[app_unexpander RType.fn]
-- def unexpandRiseTypePi : Unexpander
--   | `($(_) $l $r) => `(($l → $r))
--   | _ => throw ()



-- def RData.ismvar : RData → Bool
--   | .mvar .. => true
--   | _ => false

-- def RNat.liftmvars (n : Nat) : RNat → RNat
--   | .mvar id un => .mvar (id + n) un
--   | .bvar id un => .bvar id un
--   | .nat k      => .nat k

-- def RData.liftmvars (n : Nat) : RData → RData
--   | .bvar n un  => .bvar n un
--   | .mvar id un => .mvar (id + n) un
--   | .array k d  => .array (k.liftmvars n) (d.liftmvars n)
--   | .pair l r   => .pair (l.liftmvars n) (r.liftmvars n)
--   | .index k    => .index (k.liftmvars n)
--   | .scalar     => .scalar
--   | .vector k   => .vector (k.liftmvars n)

-- def RType.liftmvars (n : Nat) : RType → RType
--   | .pi bk pc un b   => .pi bk pc un (b.liftmvars n)
--   | .fn bt b    => .fn (bt.liftmvars n) (b.liftmvars n)
--   | .data dt    => .data (dt.liftmvars n)



-- def RNat.mapMVars (f : Nat → String → (Nat × String)) : RNat → RNat
--   | .mvar id un => let (nId, nUn) := f(id un); .mvar nId nUn
--   | .bvar id un => .bvar id un
--   | .nat k      => .nat k

-- def RData.mapMVars (f : Nat → String → (Nat × String) ) : RData → RData
--   | .bvar n un  => .bvar n un
--   | .mvar id un => .mvar (id + n) un
--   | .array k d  => .array (k.mapMVars n) (d.mapMVars n)
--   | .pair l r   => .pair (l.mapMVars n) (r.mapMVars n)
--   | .index k    => .index (k.mapMVars n)
--   | .scalar     => .scalar
--   | .vector k   => .vector (k.mapMVars n)

-- def RType.mapMVars (f : Nat → String → (Nat × String) ) : RType → RType
--   | .pi bk b   => .pi bk (b.mapMVars n)
--   | .fn bt b    => .fn (bt.mapMVars n) (b.mapMVars n)
--   | .data dt    => .data (dt.mapMVars n)


-- #reduce [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1].liftmvars 5


-- private def RNat.getmvarsAux : RNat → Array (Nat × String × RKind) → Array (Nat × String × RKind)
--   | .mvar id un, acc => acc.push (id, un, .nat)
--   | .bvar _id _un, acc => acc
--   | .nat _k, acc      => acc

-- private def RData.getmvarsAux : RData → Array (Nat × String × RKind) → Array (Nat × String × RKind)
--   | .bvar _n _un, acc  => acc
--   | .mvar id un, acc => acc.push (id, un, .data)
--   | .array k d, acc  => d.getmvarsAux (k.getmvarsAux acc)
--   | .pair l r, acc   => r.getmvarsAux (l.getmvarsAux acc)
--   | .index k, acc    => k.getmvarsAux acc
--   | .scalar, acc     => acc
--   | .vector k, acc   => k.getmvarsAux acc


-- private def RType.getmvarsAux : RType → Array (Nat × String × RKind) → Array (Nat × String × RKind)
--   | .pi _bk _pc _un b, acc   => b.getmvarsAux acc
--   | .fn bt b, acc    => b.getmvarsAux (bt.getmvarsAux acc)
--   | .data dt, acc    => dt.getmvarsAux acc

-- -- now have to deduplicate and sort. very silly approach but it works for now.
-- def RType.getmvars (t : RType) : Array (String × RKind) :=
--   let sorted := (t.getmvarsAux #[]).qsort (fun (n1, _, _) (n2, _, _) => n1 ≤ n2)
--   let deduped := sorted.foldl (fun acc x =>
--     if acc.any (fun y => y == x) then acc else acc.push x) #[]
--   deduped.map (fun (_, s, r) => (s, r))

-- #eval [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1].getmvars

-- def RType.countUniqueMVars : RType → Nat := (· |>.getmvars |>.size)
-- def RType.countUniqueMVars' : RType → Nat := Array.size ∘ RType.getmvars

-- def RType.subst (x : RType) (v : RType) (t : RType) : RType :=
--   match

def RData.substdata (x : RData) (v : RData) (t : RData) : RData :=
  match x with
  | .array n ad => if x == v then t else .array n (ad.substdata v t)
  | .pair l r => if x == v then t else .pair (l.substdata v t) (r.substdata v t)
  | _ => if x == v then t else x
  -- | .bvar
  -- | .mvar
  -- | .index
  -- | .scalar
  -- | .vector


-- x[v → t] -- should ignore username?
def RType.substdata (x : RType) (v : RData) (t : RData) : RType :=
  match x with
  | .data dt => if dt == v then .data t else .data <| dt.substdata v t
  | .pi bk pc un b => .pi bk pc un (b.substdata v t)
  | .fn bt b => .fn (bt.substdata v t) (b.substdata v t)


def RType.ismvardata : RType → Bool
  | .data (.mvar ..) => true
  | _ => false

-- def RType.tryUnifyData (x : RType) (t : RType) : RType :=
--   match x, t with
--   | .data m@(.mvar ..), .data .. => x.substdata m t
--   | _, _ => panic! s!"unexpected unify: {repr x} with {repr t}"

def RType.gettopmvar : RType → Option RData
  | .data m@(.mvar ..) => some m
  | _ => none

def RType.getRKind : RType → RKind
  | .data .. => .data
  | _ => .type -- not sure if correct
  -- never .nat? is my model wrong?


def RNat.bvar2mvar (rn : RNat) (n : RBVarId) (m : RMVarId) : RNat :=
  match rn with
  | .bvar bn un => if bn == n then .mvar m un else rn
  | .mvar .. => rn
  | .nat .. => rn
  | .plus p q => .plus (p.bvar2mvar n m) (q.bvar2mvar n m)
  | .minus p q => .minus (p.bvar2mvar n m) (q.bvar2mvar n m)
  | .mult p q => .mult (p.bvar2mvar n m) (q.bvar2mvar n m)
  | .pow p q => .pow (p.bvar2mvar n m) (q.bvar2mvar n m)

def RData.bvar2mvar (dt : RData) (n : RBVarId) (m : RMVarId) : RData :=
  match dt with
  | .bvar bn un => if bn == n then .mvar m un else dt
  | .array rn dt => .array (rn.bvar2mvar n m) (dt.bvar2mvar n m)
  | .pair dt1 dt2 => .pair (dt1.bvar2mvar n m) (dt2.bvar2mvar n m)
  | .index rn => .index (rn.bvar2mvar n m)
  | .vector rn d => .vector (rn.bvar2mvar n m) (d.bvar2mvar n m)
  | .mvar .. | .scalar .. | .natType => dt

def RType.bvar2mvar (t : RType) (mid : RMVarId) : RType :=
  go t 0 mid where
  go : RType → RBVarId → RMVarId → RType
  | .data dt, n, m => .data (dt.bvar2mvar n m)
  | .pi bk pc un b, n, m => .pi bk pc un (go b (n+1) m)
  | .fn bt b, n, m => .fn (go bt n m) (go b n m)

def RNat.rnatbvar2rnat (rn : RNat) (n : RBVarId) (rnat : RNat) : RNat :=
  match rn with
  | .bvar bn .. => if bn == n then rnat else rn
  | .mvar .. => rn
  | .nat .. => rn
  | .plus p q => .plus (p.rnatbvar2rnat n rnat) (q.rnatbvar2rnat n rnat)
  | .minus p q => .minus (p.rnatbvar2rnat n rnat) (q.rnatbvar2rnat n rnat)
  | .mult p q => .mult (p.rnatbvar2rnat n rnat) (q.rnatbvar2rnat n rnat)
  | .pow p q => .pow (p.rnatbvar2rnat n rnat) (q.rnatbvar2rnat n rnat)

def RData.rnatbvar2rnat (dt : RData) (n : RBVarId) (rnat : RNat) : RData :=
  match dt with
  | .array rn dt => .array (rn.rnatbvar2rnat n rnat) (dt.rnatbvar2rnat n rnat)
  | .pair dt1 dt2 => .pair (dt1.rnatbvar2rnat n rnat) (dt2.rnatbvar2rnat n rnat)
  | .index rn => .index (rn.rnatbvar2rnat n rnat)
  | .vector rn d => .vector (rn.rnatbvar2rnat n rnat) (d.rnatbvar2rnat n rnat)
  | .scalar .. | .bvar .. | .mvar .. | .natType => dt

def RType.rnatbvar2rnat (t : RType) (rnat : RNat) : RType :=
  go t 0 rnat where
  go : RType → RBVarId → RNat → RType
  | .data dt, n, rnat => .data (dt.rnatbvar2rnat n rnat)
  | .pi bk pc un b, n, rnat => .pi bk pc un (go b (n+1) rnat)
  | .fn bt b, n, rnat => .fn (go bt n rnat) (go b n rnat)


def RData.rdatabvar2rdata (dt : RData) (n : RBVarId) (rdata : RData) : RData :=
  match dt with
  | .bvar bn .. => if bn == n then rdata else dt
  | .array rn dt => .array rn (dt.rdatabvar2rdata n rdata)
  | .pair dt1 dt2 => .pair (dt1.rdatabvar2rdata n rdata) (dt2.rdatabvar2rdata n rdata)
  | .index rn => .index rn
  | .vector rn d => .vector rn (d.rdatabvar2rdata n rdata)
  | .scalar .. | .mvar .. | .natType => dt

def RType.rdatabvar2rdata (t : RType) (rdata : RData) : RType :=
  go t 0 rdata where
  go : RType → RBVarId → RData → RType
  | .data dt, n, rdata => .data (dt.rdatabvar2rdata n rdata)
  | .pi bk pc un b, n, rdata => .pi bk pc un (go b (n+1) rdata)
  | .fn bt b, n, rdata => .fn (go bt n rdata) (go b n rdata)



-- #eval [RiseT| (n : nat) →(m:nat)→ n·scalar].rnatbvar2rnat <| .nat 9
-- #eval (RType.pi RKind.nat RBinderInfo.explicit `n (RType.pi RKind.nat RBinderInfo.explicit `m (RType.data (RData.array (RNat.bvar 1 `n) RData.scalar)))).rnatbvar2rnat <| .nat 9
-- #eval ((RType.pi RKind.nat RBinderInfo.explicit `m (RType.data (RData.array (RNat.bvar 1 `n) RData.scalar)))).rnatbvar2rnat <| .nat 9

-- #eval (RType.pi RKind.nat RBinderInfo.explicit `n
--         ((RType.data (RData.array ((RNat.bvar 2 `n).plus (RNat.mvar 0 `m)) (RData.mvar 1 `t))).fn
--           (RType.data (RData.array (RNat.bvar 2 `n) (RData.mvar 1 `t))))).rnatbvar2rnat <| .nat 5
-- #eval (--RType.pi RKind.nat RBinderInfo.explicit `n
--         ((RType.data (RData.array ((RNat.bvar 2 `n).plus (RNat.mvar 0 `m)) (RData.mvar 1 `t))).fn
--           (RType.data (RData.array (RNat.bvar 2 `n) (RData.mvar 1 `t))))).rnatbvar2rnat <| .nat 5
