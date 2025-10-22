import Rise.Basic
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
  rnatEqualities : List (RNat × RNat) := []
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
