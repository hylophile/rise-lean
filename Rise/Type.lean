import Lean
import Rise.Prelude
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
syntax num                    : rise_nat
syntax ident                  : rise_nat

syntax "[RiseN|" rise_nat "]" : term

partial def elabToRNat : Syntax → RElabM RNat
  | `(rise_nat| $n:num) => return RNat.nat n.getNat
  | `(rise_nat| $x:ident) => do
    let kctx ← getKCtx
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some idx =>
      return RNat.bvar idx x.getId.toString
    | none => throwErrorAt x s!"rnat: unknown identifier {mkConst x.getId}"
    -- | none =>
    --   let mctx ← getMVCtx
    --   match mctx.reverse.findIdx? (λ (name, _, _) => name == x.getId) with
    --   | some idx =>
    --     return RNat.mvar idx x.getId.toString
    --   | none => throwErrorAt x s!"rnat: unknown identifier {mkConst x.getId}"
  | _ => throwUnsupportedSyntax

instance : ToExpr RNat where
  toExpr e := match e with
  | RNat.bvar deBruijnIndex userName =>
    let f := mkConst ``RNat.bvar
    mkAppN f #[mkNatLit deBruijnIndex, mkStrLit userName]
  | RNat.mvar id userName =>
    let f := mkConst ``RNat.mvar
    mkAppN f #[mkNatLit id, mkStrLit userName]
  | RNat.nat n =>
    let f := mkConst ``RNat.nat
    mkAppN f #[mkNatLit n]
  toTypeExpr := mkConst ``RNat

partial def elabRNat : Syntax → RElabM Expr
  | stx => do
    let n ← elabToRNat stx
    return toExpr n



-- def RData.beq (a : RData) (b : RData) : Bool :=
--     match a, b with
--     | .bvar ia _, .bvar ib _ => ia == ib
--     | .mvar ia _, .mvar ib _ => true -- <- very likely incorrect :D -- ia == ib
--     | .array na da,.array nb db => na == nb && da.beq db
--     | .pair da1 da2,.pair db1 db2 => da1.beq db1 && da2.beq db2
--     | .index ia,.index ib => ia == ib
--     | .scalar, .scalar => true
--     | .vector na, .vector nb => na == nb
--     | _, _ => false

-- instance : BEq RData where
--   beq := RData.beq


declare_syntax_cat rise_data
syntax:50 rise_nat "·" rise_data:50 : rise_data
syntax:50 "scalar"                  : rise_data
syntax:10 rise_data "×" rise_data   : rise_data
syntax    ident                     : rise_data
syntax    "idx[" rise_nat "]"       : rise_data
syntax    rise_nat "<" "scalar" ">" : rise_data
syntax    "(" rise_data ")"         : rise_data

partial def elabToRData : Syntax → RElabM RData
  | `(rise_data| scalar) => return RData.scalar

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

  | `(rise_data| $n:rise_nat < scalar >) => do
    let n <- elabToRNat n
    return RData.vector n

  | `(rise_data| ($d:rise_data)) =>
    elabToRData d

  | _ => throwUnsupportedSyntax

instance : ToExpr RData where
  toExpr :=
    let rec go : RData → Expr
    | RData.scalar => mkConst ``RData.scalar
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
    | RData.vector n =>
      mkAppN (mkConst ``RData.vector) #[toExpr n]
    go
  toTypeExpr := mkConst ``RData

partial def elabRData : Syntax → RElabM Expr
  | stx => do
    let d ← elabToRData stx
    return toExpr d

instance : ToExpr Plicity where
  toExpr e := match e with
  | Plicity.ex => mkConst ``Plicity.ex
  | Plicity.im => mkConst ``Plicity.im
  toTypeExpr := mkConst ``Plicity


-- only for Check::infer! to be able to panic
instance : Inhabited RType where
  default := RType.data .scalar


declare_syntax_cat rise_type
syntax rise_data                                  : rise_type
syntax rise_type "→" rise_type                    : rise_type
syntax "(" rise_type ")"                          : rise_type
syntax "{" ident+ ":" rise_kind "}" "→" rise_type : rise_type
syntax "(" ident ":" rise_kind ")" "→" rise_type  : rise_type

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
    return RType.pi t body

  | `(rise_type| ($t:rise_type)) => do
    elabToRType t

  | `(rise_type| {$x:ident : $k:rise_kind} → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← withNewType (x.getId, k) do elabToRType t
    return RType.upi k Plicity.im x.getId body

  | `(rise_type| ($x:ident : $k:rise_kind) → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← withNewType (x.getId, some k) do elabToRType t
    return RType.upi k Plicity.ex x.getId body
  | _ => throwUnsupportedSyntax

instance : ToExpr RType where
  toExpr :=
    let rec go : RType → Expr
    | RType.data d =>
      let f := mkConst ``RType.data
      mkAppN f #[toExpr d]
    | RType.upi binderKind pc userName body =>
      let f := mkConst ``RType.upi
      mkAppN f #[toExpr binderKind, toExpr pc, toExpr userName, go body]
    | RType.pi binderType body =>
      let f := mkConst ``RType.pi
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
@[app_unexpander RType.pi]
def unexpandRiseTypePi : Unexpander
  | `($(_) $l $r) => `(($l → $r))
  | _ => throw ()


#check [RiseT| {n : nat} → {s : data} → {t : data} → n·(s × t) → (n·s × n·t)]
-- #check [RiseT| {n t : data} → n·t → n·t × n·t]
#check [RiseT| scalar]
#check [RiseT| scalar → scalar ]
#check [RiseT| {δ : data} → δ → δ → δ]
#check [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1]
#guard [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1] ==
  RType.upi RKind.data Plicity.im `δ1
        (RType.upi RKind.data Plicity.im `δ2
          ((RType.data ((RData.bvar 1 `δ1).pair (RData.bvar 0 `δ2))).pi (RType.data (RData.bvar 1 `δ1))))


#check [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n·δ1 → n·δ2]

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
--   | .upi bk pc un b   => .upi bk pc un (b.liftmvars n)
--   | .pi bt b    => .pi (bt.liftmvars n) (b.liftmvars n)
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
--   | .upi bk b   => .upi bk (b.mapMVars n)
--   | .pi bt b    => .pi (bt.mapMVars n) (b.mapMVars n)
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
--   | .upi _bk _pc _un b, acc   => b.getmvarsAux acc
--   | .pi bt b, acc    => b.getmvarsAux (bt.getmvarsAux acc)
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
  | .upi bk pc un b => .upi bk pc un (b.substdata v t)
  | .pi bt b => .pi (bt.substdata v t) (b.substdata v t)


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

def RData.bvar2mvar (dt : RData) (n : RBVarId) (m : RMVarId) : RData :=
  match dt with
  | .bvar bn un => if bn == n then .mvar m un else dt
  | .mvar .. => dt
  | .array rn dt => .array (rn.bvar2mvar n m) (dt.bvar2mvar n m)
  | .pair dt1 dt2 => .pair (dt1.bvar2mvar n m) (dt2.bvar2mvar n m)
  | .index rn => .index (rn.bvar2mvar n m)
  | .scalar => dt
  | .vector rn => .vector (rn.bvar2mvar n m)


def RType.bvar2mvar (t : RType) (mid : RMVarId) : RType :=
  go t 0 mid where
  go : RType → RBVarId → RMVarId → RType
  | .data dt, n, m => .data (dt.bvar2mvar n m)
  | .upi bk pc un b, n, m => .upi bk pc un (go b (n+1) m)
  | .pi bt b, n, m => .pi (go bt n m) (go b n m)
