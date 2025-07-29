import RiseLean.Prelude
import Lean

open Lean

namespace RiseM

structure State where
  mctx : MVCtx
  kctx : KCtx
  tctx : TCtx

abbrev Error := String

abbrev _root_.RiseM := StateT State (Except Error)

def getMCtx : RiseM MVCtx := State.mctx <$> get
def getKCtx : RiseM KCtx  := State.kctx <$> get
def getTCtx : RiseM TCtx  := State.tctx <$> get

-- Runs a given `RiseM` computation with a given mvar context, and restores the context afterwards.
def withMCtx (mctx : MVCtx) (m : RiseM α) : RiseM α := do
  let { mctx := before, .. } ← getModify ({ · with mctx })
  let result ← m
  modify ({ · with mctx := before })
  return result

-- Runs a given `RiseM` computation with a given kind context, and restores the context afterwards.
def withKCtx (kctx : KCtx) (m : RiseM α) : RiseM α := do
  let { kctx := before, .. } ← getModify ({ · with kctx })
  let result ← m
  modify ({ · with kctx := before })
  return result

-- Runs a given `RiseM` computation with a given type context, and restores the context afterwards.
def withTCtx (tctx : TCtx) (m : RiseM α) : RiseM α := do
  let { tctx := before, .. } ← getModify ({ · with tctx })
  let result ← m
  modify ({ · with tctx := before })
  return result

-- Runs a given `RiseM` computation and restores the mvar context afterwards.
def withRestoringMCtx (m : RiseM α) : RiseM α := do
  withMCtx (← getMCtx) m

-- Runs a given `RiseM` computation with an additional given mvar, and restores the mvar context
-- afterwards.
-- Important: Any changes made to the mvar context in `m` will not be persisted!
def withMVar (name : Name) (kind : RKind) (type : Option RType) (m : RiseM α) : RiseM α := do
  withMCtx (m := m) <| (← getMCtx).push (name, kind, type)

-- Runs a given `RiseM` computation with an additional given type variable, and restores the type
-- context afterwards.
-- Important: Any changes made to the type context in `m` will not be persisted!
def withTVar (name : Name) (type : Option RType) (m : RiseM α) : RiseM α := do
  withTCtx (m := m) <| (← getTCtx).push (name, type)

-- Adds a given mvar to the mvar context.
def addMVar (name : Name) (kind : RKind) (type : Option RType) : RiseM Unit := do
  modify fun state => { state with mctx := state.mctx.push (name, kind, type) }
