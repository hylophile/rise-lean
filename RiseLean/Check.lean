import RiseLean.Prelude
import RiseLean.RElabM
import RiseLean.Expr
import RiseLean.Type
import RiseLean.Unification

-- set_option linter.unusedVariables false
--

-- partial def addImplicits (t: RType) : RElabM RType := do
--   match t with
--   | .upi bk .im un b => do
--     let mid ← getFreshMVarId
--     addMVar mid un bk none
--     let newB := b.bvar2mvar mid
--     addImplicits newB
--   | x => return x

-- partial def inferAux (e: RExpr) : RElabM RType := do
--   -- dbg_trace (repr e)
--   match e with
--   | .const un => match (← findConst? un) with
--     | some t => return t
--     | none => throwError "unknown identifier {un}"
    
--   | .lam un bt body =>
--     match bt with
--     | .some t =>
--       let body := body.bvar2fvar un -- why does this call cause "fail to show termination?"
--       let bodyt ← withNewLocalTerm (un, bt) do inferAux body
--       return .pi t bodyt
--     | none =>
--       let body := body.bvar2fvar un -- why does this call cause "fail to show termination?"
--       let id ← getFreshMVarId
--       addMVar id Lean.Name.anonymous RKind.data  
--       let t :=  RType.data (.mvar id Lean.Name.anonymous)
--       let bodyt ← withNewLocalTerm (un, t) do inferAux body
--       let t ← applyUnifyResultsUntilStable t
--       -- let bodyt ← applyUnifyResults bodyt
--       return .pi t bodyt

--   | .ulam un bk body =>
--     throwError "todo ulam"
--     -- match bk with
--     -- | some bk =>
--     --   let (bodyt, s) ← withNewMVar ("todo".toName, bk, none) do inferAux s body
--     --   return (.upi bk .ex "todo" bodyt, s)
--     -- | none => throwError "todo: infer ulam arg without annotation"

--   | .fvar id =>
--     match (← findLocal? id) with
--     | some t => return t
--     | none => throwError "fvar {id} not in context"

--   | .bvar id =>
--     throwError "unexpected bvar {id}"

--   | .lit _ => return RType.data .scalar

--   | .app f e =>
--     let ft ← inferAux f
--     let ft ← addImplicits ft
--     let et ← inferAux e
--     let et ← addImplicits et
--     match ft with
--     | .pi blt brt =>
--       match blt.unify et with
--       | some sub =>
--         addSubst sub
--         return brt.apply sub
--         -- applyUnifyResults brt
--       | none =>
--         throwError s!"\n{repr f}\n\n{repr e}\n\ncannot unify {blt} with {et}"
--     | .upi bk .im un b =>
--       throwError s!"unexpected upi {ft}"
--     | _ => throwError s!"not a function type: {ft}"


-- -- -- TODO: translate example programs in shine/src/test/scala/rise/core
-- -- -- /home/n/tub/masters/shine/src/test/scala/apps
-- -- --
-- -- --
-- --
-- --
