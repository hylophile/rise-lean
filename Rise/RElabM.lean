import Rise.Basic
import Rise.Unification
import Lean
open Lean Elab.Command

structure RContext where
  gtctx : TCtx := #[]
  ltctx : TCtx := #[]
  kctx : KCtx := #[]
  -- mctx : MVCtx
  -- debug : Bool := false
  -- depth : Nat := 0

structure RState where
  unifyResult : Substitution := []
  nextMVarId : RMVarId := 0
  mvars : Lean.PersistentHashMap RMVarId MetaVarDeclaration := {}

abbrev RElabM := ReaderT RContext <| StateRefT RState Lean.Elab.TermElabM

def defaultState : RState := {}
def defaultContext : RContext := {}

def liftToTermElabMWith (ctx : RContext) (initialState : RState) (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run ctx |>.run initialState
  return result

def liftToTermElabM (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run defaultContext |>.run defaultState
  return result
  
-- def liftToCommandElabM (x : RElabM α) : CommandElabM α := do
--   let (result, _) ← x.run defaultContext |>.run defaultState
--   return result

def getFreshMVarId : RElabM RMVarId := do
  let rstate : RState ← get
  set { rstate with nextMVarId := rstate.nextMVarId + 1 }
  return rstate.nextMVarId

def addMVar (id : RMVarId) (userName : Lean.Name) (kind : RKind) (type : Option RType := none) : RElabM Unit := do
  let rstate : RState ← get
  set { rstate with mvars := rstate.mvars.insert id { userName, kind, type } }
  return ()

def findMVar? (id : RMVarId) : RElabM <| Option MetaVarDeclaration := do
  let rstate : RState ← get
  return rstate.mvars.find? id

unsafe def addSubst (subst : Substitution) : RElabM Unit := do
  let unifyResults : Substitution := (← get).unifyResult
  subst.forM (λ x@(mv, se) =>
    match unifyResults.find? (λ (mvv, _) => mvv == mv) with
    | some (_, see) => match se, see with
      | .data dt1, .data dt2 =>
        match unifyOneRData dt1 dt2 with
        | some s => do
          -- dbg_trace ("!!!adding\n", toString s, "\n",dt1, dt2,"\n\n")
          -- dbg_trace ("because", x,"\n\n!!")
          -- let x ← addSubst s
          addSubst s
          -- modify (λ r => {r with unifyResult := x }) --s ++ r.unifyResult})
        | none => throwError "unify error while addSubst"
      | _,_ => throwError "handle nats!"
    | none => modify (λ r => {r with unifyResult := x :: r.unifyResult})
  )
  
  -- modify (λ r => {r with unifyResult := s ++ r.unifyResult})

def applyUnifyResults (t : RType) : RElabM RType := do
  let unifyResults : Substitution := (← get).unifyResult
  return t.apply unifyResults

def applyUnifyResultsUntilStable (x : RType) (fuel : Nat := 100) : RElabM RType := do
  let unifyResults : Substitution := (← get).unifyResult
  let rec loop (current : RType) (remaining : Nat) : RElabM RType :=
    if remaining = 0 then throwError "fuel ran out"
    else
      let next := current.apply unifyResults
      if next == current then return current
      else loop next (remaining - 1)
  loop x fuel

partial def applyUnifyResultsRecursivelyUntilStable (e : TypedRExpr) : RElabM TypedRExpr := do
  let newt := (← applyUnifyResultsUntilStable e.type) 
  match e.node with
  | .app e1 e2 => return ⟨.app (← applyUnifyResultsRecursivelyUntilStable e1) (← applyUnifyResultsRecursivelyUntilStable e2), newt⟩
  | .lam un t b => return ⟨.lam un (← applyUnifyResultsUntilStable t) (← applyUnifyResultsRecursivelyUntilStable b), newt⟩
  | .deplam un k b => return ⟨.deplam un k (← applyUnifyResultsRecursivelyUntilStable b), newt⟩
  | _ => return ⟨e.node, newt⟩


def withNewLocalTerm (arg : TCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with ltctx := ctx.ltctx.push arg })

def withNewGlobalTerm (arg : TCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with gtctx := ctx.gtctx.push arg })

def findConst? (n : Lean.Name) : RElabM <| Option RType := do
  let gtctx := (← read).gtctx
  return match gtctx.find? (λ (name, _) => name == n) with
  | some (_, rtype) => rtype
  | none => none

def findLocal? (n : Lean.Name) : RElabM <| Option RType := do
  let ltctx := (← read).ltctx
  return match ltctx.find? (λ (name, _) => name == n) with
  | some (_, rtype) => rtype
  | none => none

def findTypeVar? (n : Lean.Name) : RElabM <| Option RKind := do
  let kctx := (← read).kctx
  return match kctx.find? (λ (name, _) => name == n) with
  | some (_, rkind) => rkind
  | none => none

def ur : RElabM Substitution := do
  return (← get).unifyResult


def withNewTVar (arg : KCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

-- def withNewMVCTx (f : MVCtx → MVCtx) : RElabM α → RElabM α :=
-- withReader (fun ctx => { ctx with mctx := f ctx.mctx })

def withNewType (arg : KCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

def getLTCtx : RElabM TCtx := do
  return (← read).ltctx

def getGTCtx : RElabM TCtx := do
  return (← read).gtctx

def getKCtx : RElabM KCtx := do
  return (← read).kctx

-- def getMVCtx : RElabM MVCtx := do
-- return (← read).mctx
