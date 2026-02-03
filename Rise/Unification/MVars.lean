import Rise.Basic
import Rise.Elab.RElabM

def mvarToString : Nat → String → String
  | id, nm => s!"m_{nm}_{id}"
def bvarToString : Nat → String → String
  | id, nm => s!"b_{nm}_{id}"

def RNat.mapMVars (t : RNat) (f : RMVarId → RMVarId) : RNat :=
  match t with
  | .bvar ..    => t
  | .mvar id nm => .mvar (f id) nm
  | .nat _      => t
  | .plus a b   => .plus (a.mapMVars f) (b.mapMVars f)
  | .minus a b  => .minus (a.mapMVars f) (b.mapMVars f)
  | .mult a b   => .mult (a.mapMVars f) (b.mapMVars f)
  | .div a b    => .div (a.mapMVars f) (b.mapMVars f)
  | .pow a b    => .pow (a.mapMVars f) (b.mapMVars f)

def RData.mapMVars (t : RData) (f : RMVarId → RMVarId) : RData :=
  match t with
  | .bvar ..       => t
  | .mvar id name  => .mvar (f id) name
  | .array n d     => .array (n.mapMVars f) (d.mapMVars f)
  | .pair d1 d2    => .pair (d1.mapMVars f) (d2.mapMVars f)
  | .index n       => .index (n.mapMVars f)
  | .scalar ..     => t
  | .natType       => t
  | .vector n d    => .vector (n.mapMVars f) (d.mapMVars f)

def RType.mapMVars (t : RType) (f : RMVarId → RMVarId) : RType :=
  match t with
  | .data dt => .data <| dt.mapMVars f
  | .fn a b => .fn (a.mapMVars f) (b.mapMVars f)
  | .pi k bi n b => .pi k bi n (b.mapMVars f)

mutual
partial def TypedRExprNode.mapMVars (t : TypedRExprNode) (f : RMVarId → RMVarId) : TypedRExprNode :=
  match t with
  | .bvar ..
  | .const ..
  | .lit .. => t
  | .app fn arg => .app (fn.mapTypeMVars f) (arg.mapTypeMVars f)
  | .depapp fn arg => match arg with
    | .nat v => .depapp (fn.mapTypeMVars f) (.nat <| v.mapMVars f)
    | .data v => .depapp (fn.mapTypeMVars f) (.data <| v.mapMVars f)
    | .type v => .depapp (fn.mapTypeMVars f) (.type <| v.mapMVars f)
  | .lam n t b => .lam n (t.mapMVars f) (b.mapTypeMVars f)
  | .deplam n k b => .deplam n k (b.mapTypeMVars f)


partial def TypedRExpr.mapTypeMVars (t : TypedRExpr) (f : RMVarId → RMVarId) : TypedRExpr :=
  ⟨t.node.mapMVars f, t.type.mapMVars f⟩
end


-- open Std.HashSet

def RNat.collectMVarIds (t : RNat) : Std.HashSet RMVarId :=
  match t with
  | .bvar ..    => {} --Std.HashSet.emptyWithCapacity 0
  | .mvar id _  => {id}
  | .nat _      => {}
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => a.collectMVarIds ∪ b.collectMVarIds


def RData.collectMVarIds (t : RData) : Std.HashSet RMVarId :=
  match t with
  | .bvar ..       => {}
  | .mvar id _     => {id}
  | .scalar ..     => {}
  | .natType       => {}
  | .array n d     => n.collectMVarIds ∪ d.collectMVarIds
  | .pair d1 d2    => d1.collectMVarIds ∪ d2.collectMVarIds
  | .index n       => (n.collectMVarIds)
  | .vector n d    => n.collectMVarIds ∪ d.collectMVarIds


def RType.collectMVarIds (t : RType) : Std.HashSet RMVarId :=
  match t with
  | .data dt => dt.collectMVarIds
  | .fn a b => a.collectMVarIds ∪ b.collectMVarIds
  | .pi _ _ _ b => (b.collectMVarIds)

partial def TypedRExpr.collectMVarIds  (e : TypedRExpr) : Std.HashSet RMVarId :=
  let t_mvars := e.type.collectMVarIds
  let n_mvars := match e.node with
    | .bvar ..
    | .const ..
    | .lit .. => {}
    | .app fn arg => fn.collectMVarIds ∪ arg.collectMVarIds
    | .depapp fn arg => match arg with
      | .nat v => v.collectMVarIds ∪ fn.collectMVarIds
      | .data v => v.collectMVarIds ∪ fn.collectMVarIds
      | .type v => v.collectMVarIds ∪ fn.collectMVarIds
    | .lam _ t b => t.collectMVarIds ∪ b.collectMVarIds
    | .deplam _ _ b => b.collectMVarIds
  t_mvars ∪ n_mvars


def RNat.collectMVars : RNat → List String
  | .bvar ..    => []
  | .mvar id nm => [mvarToString id nm.toString]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectMVars a ++ collectMVars b

def RNat.collectBVars : RNat → List String
  | .mvar ..    => []
  | .bvar id nm => [bvarToString id nm.toString]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectBVars a ++ collectBVars b

def collectMVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectMVars ++ r.collectMVars) |> List.flatten

def collectBVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectBVars ++ r.collectBVars) |> List.flatten

def collectVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectBVars ++ r.collectBVars ++ l.collectMVars ++ r.collectMVars) |> List.flatten |> List.eraseDups

-- takes an expr with possibly conflicting mvarIds and maps them to fresh mvarIds in the current context.
def shiftMVars (e : TypedRExpr) : RElabM TypedRExpr := do
  let mvars := e.collectMVarIds
  let map : Std.HashMap RMVarId RMVarId ← mvars.foldM (init := Std.HashMap.emptyWithCapacity)
    (fun m a => do
      let x ← getFreshMVarId
      pure <| m.insert a x)
  return e.mapTypeMVars (fun id => map[id]!)

def sane (n: Lean.Name) : String :=
  if n == Lean.Name.anonymous then "anonymous" else toString n
