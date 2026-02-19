import Rise.Basic
import Rise.Elab.RElabM
import Lean

-- unification algorithm adapted from
-- https://web.archive.org/web/20250713140859/http://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm


inductive UnificationError
  | structural (l r : SubstEnum)
  | structuralType (l r : RType)
  | unsolved (msg : String)
deriving Repr, BEq

def UnificationResult := Except UnificationError Substitution

instance : ToString UnificationError where
  toString x := match x with
  | .structural l r => s!"structural: {l} != {r}"
  | .structuralType l r => s!"structural: {l} != {r}"
  | .unsolved s => s!"solver: {s}"

instance : ToString UnificationResult where
  toString x := match x with
  | .ok s => s!"{s}"
  | .error s => s!"{s}"

instance : Repr UnificationResult where
  reprPrec x _ :=
    match x with
    | .ok a    => s!".ok {a}"
    | .error e => s!".error {repr e}"

def UnificationResult.merge : UnificationResult → UnificationResult → UnificationResult
  | .ok l, .ok r => .ok <| l ++ r
  | .error e, .ok _ | .ok _, .error e => .error e
  | .error e1, .error e2 => .error <| .unsolved s!"{e1}\n{e2}"
  
mutual
def unifyOneRNat (s t : RNat) : RElabM UnificationResult :=
  do
  addRNatEquality (s,t)
  return .ok []

def unifyRNat (equations : List (RNat × RNat)) : RElabM UnificationResult :=
  match equations with
  | [] => return .ok []
  | (x, y) :: rest => do
    let tailSubst ← unifyRNat rest
    match tailSubst with
    | .ok tailSubst =>
      let x' := x.apply tailSubst
      let y' := y.apply tailSubst

      let headSubst ← unifyOneRNat x' y'
      match headSubst with
      | .ok headSubst =>
        return .ok <| headSubst ++ tailSubst
      | e => return e
    | e => return e
end

mutual
partial def unifyOneRData (s t : RData) : RElabM UnificationResult :=
  match s, t with
  | .mvar x _, .mvar y _ =>
    if x == y then return .ok [] else return .ok [(x, .data t)]

  | .mvar x _, term | term, .mvar x _ =>
    if term.has x then
      return .error <| .structural (.data s) (.data t)
    else
      return .ok [(x, .data term)]

  | .bvar n1 _, .bvar n2 _ =>
    if n1 == n2 then return .ok [] else return .error <| .structural (.data s) (.data t)

  | .array k1 d1, .array k2 d2 => do
    return (← unifyRNat [(k1, k2)])  |>.merge (← unifyRData [(d1, d2)])

  | .posDepArray k1 d1, .posDepArray k2 d2 => do
    return (← unifyRNat [(k1, k2)])  |>.merge (← unifyRData [(d1.body, d2.body)])

  | .pair l1 r1, .pair l2 r2 =>
    unifyRData [(l1, l2), (r1, r2)]

  | .depPair _ d1, .depPair _ d2 => do
    return (← unifyRData [(d1, d2)])

  | .index k1, .index k2 =>
    unifyOneRNat k1 k2

  | .scalar x, .scalar y => if x == y then return .ok [] else return .error <| .structural (.data s) (.data t)

  | .natType, .natType => return .ok []

  | .vector k1 d1, .vector k2 d2 => do
    return (← unifyRNat [(k1, k2)])  |>.merge (← unifyRData [(d1, d2)])

  | _, _ => return .error <| .structural (.data s) (.data t)

partial def unifyRData (equations : List (RData × RData)) : RElabM UnificationResult :=
  match equations with
  | [] => return .ok []
  | (x, y) :: t => do
    let t2 <- unifyRData t
    match t2 with
    | .ok t2 =>
      let t1 <- unifyOneRData (x.apply t2) (y.apply t2)
      match t1 with
      | .ok t1 => return .ok <| t1 ++ t2
      | e => return e
    | e => return e
end

partial def RData.unify (l r : RData) : RElabM UnificationResult :=
  let result := unify l r
  result

mutual
partial def unifyOneRType (s t : RType) : RElabM UnificationResult :=
  match s, t with
  | .data dt1, .data dt2 =>
    unifyRData [(dt1, dt2)]

  | .pi bk1 pc1 _ body1, .pi bk2 pc2 _ body2 =>
    if bk1 == bk2 && pc1 == pc2 then
      unifyRType [(body1, body2)]
    else
      return .error <| .structuralType s t

  | .fn binderType1 body1, .fn binderType2 body2 =>
    unifyRType [(binderType1, binderType2), (body1, body2)]

  | _, _ => return .error <| .structuralType s t

partial def unifyRType (equations : List (RType × RType)) : RElabM UnificationResult :=
  match equations with
  | [] => return .ok []
  | (x, y) :: rest => do
    let tailSubst ← unifyRType rest
    match tailSubst with
    | .ok tailSubst =>
      let x' := x.apply tailSubst
      let y' := y.apply tailSubst

      let headSubst ← unifyOneRType x' y'
      match headSubst with
      | .ok headSubst =>
        return .ok <| headSubst ++ tailSubst
      | e => return e
    | e => return e
end

def RType.unify (l r : RType) : RElabM UnificationResult :=
  unifyRType [(l, r)]

def unify := RType.unify

partial def addSubst (stx : Lean.Syntax) (subst : Substitution) : RElabM Unit := do
  let unifyResults : Substitution := (← get).unifyResult
  subst.forM (λ x@(mv, se) =>
    match unifyResults.find? (λ (mvv, _) => mvv == mv) with
    | some (_, see) => match se, see with
      | .data dt1, .data dt2 => do
        match ← unifyOneRData dt1 dt2 with
        | .ok s => do
          addSubst stx s
        | .error x => throwErrorAt stx "unify error while addSubst ({x})"
      | .nat n1, .nat n2 => do
        match ← unifyOneRNat n1 n2 with
        | .ok s => do
          addSubst stx s
        | .error x => throwErrorAt stx "unify error while addSubst ({x})"
      | _,_ => throwError "weird addSubst error"
    | none => modify (λ r => {r with unifyResult := x :: r.unifyResult})
  )

def stabilizeUnifyResultsAux (x : SubstEnum) (s : Substitution) : RElabM SubstEnum :=
  let fuel := 100
  let rec loop (current : SubstEnum) (remaining : Nat) : RElabM SubstEnum :=
    if remaining = 0 then throwError "fuel ran out"
    else
      let next := current.apply s
      if next == current then return current
      else loop next (remaining - 1)
  loop x fuel

def stabilizeUnifyResults : RElabM Unit := do
  let unifyResult : Substitution := (← get).unifyResult
  let new ← unifyResult.mapM (fun (k,v) => do
    let v ← stabilizeUnifyResultsAux v unifyResult
    return (k, v)
  )
  modify (λ r => {r with unifyResult := new})
  return ()

def RType.applyUnifyResults (t : RType) : RElabM RType := do
  let unifyResults : Substitution := (← get).unifyResult
  return t.apply unifyResults

partial def TypedRExpr.applyUnifyResults (e : TypedRExpr) : RElabM TypedRExpr := do
  let newType := (← e.type.applyUnifyResults)
  match e.node with
  | .app e1 e2 => return ⟨.app (← e1.applyUnifyResults) (← e2.applyUnifyResults), newType⟩
  | .lam un t b => return ⟨.lam un (← t.applyUnifyResults) (← b.applyUnifyResults), newType⟩
  | .deplam un k b => return ⟨.deplam un k (← b.applyUnifyResults), newType⟩
  | _ => return ⟨e.node, newType⟩
