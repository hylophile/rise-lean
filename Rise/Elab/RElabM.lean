import Rise.Basic
import Lean
open Lean Elab.Command

structure RContext where
  gtctx : TypingContext := #[]
  ltctx : TypingContext := #[]
  kctx : KindingContext := #[]

structure RState where
  unifyResult : Substitution := []
  unifyResultMap : Std.HashMap RMVarId SubstEnum := {}
  rnatEqualities : List (RNat × RNat) := []
  unifyGoals : List (RType × RType) := []
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

def getFreshMVarId : RElabM RMVarId := do
  let rstate : RState ← get
  set { rstate with nextMVarId := rstate.nextMVarId + 1 }
  return rstate.nextMVarId

def addMVar (id : RMVarId) (userName : Lean.Name) (kind : RKind) (type : Option RType := none) : RElabM Unit := do
  let rstate : RState ← get
  set { rstate with mvars := rstate.mvars.insert id { userName, kind, type } }
  return ()

def addRNatEquality  (eq : RNat × RNat) : RElabM Unit := do
  let rstate : RState ← get
  set { rstate with rnatEqualities := eq :: rstate.rnatEqualities }
  return ()

def addUnifyGoal  (eq : RType × RType) : RElabM Unit := do
  let rstate : RState ← get
  set { rstate with unifyGoals := eq :: rstate.unifyGoals }
  return ()

def findMVar? (id : RMVarId) : RElabM <| Option MetaVarDeclaration := do
  let rstate : RState ← get
  return rstate.mvars.find? id

def withNewLocalTerm (arg : TypingContextElement) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with ltctx := ctx.ltctx.push arg })

def withNewGlobalTerm (arg : TypingContextElement) : RElabM α → RElabM α :=
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


def withNewTypeVar (arg : KindingContextElement) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

def withNewType (arg : KindingContextElement) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

def getLocalTCtx : RElabM TypingContext := do
  return (← read).ltctx

def getGlobalTCtx : RElabM TypingContext := do
  return (← read).gtctx

def getKCtx : RElabM KindingContext := do
  return (← read).kctx
