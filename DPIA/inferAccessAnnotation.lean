import DPIA.Substitutions

-- helper type
private abbrev Context := Std.HashMap TypedRExpr PhraseType
private abbrev SubstMap := Std.HashMap Lean.Name DAnnotation

---------------- substType -----------------
structure Subst where
  map : SubstMap

def Subst.applyPt (subst : Subst)(pt : PhraseType) : PhraseType :=
  subst.map.fold (fun acc key value => substituteAnnotationPt acc key value) (init := pt)

def Subst.applySubstHelper (inner : List (Lean.Name × DAnnotation)) (outer : SubstMap) : SubstMap :=
  match inner with
    | [] => outer
    | (key, value) :: ys => let val := outer.get? key
                            match val with
                              | some y => if y == value
                                            then Subst.applySubstHelper ys outer
                                            else panic! s!"Unexpectedly assigning var {key} multiple times."
                              | none => let new := outer.insert key value
                                        Subst.applySubstHelper ys new

def Subst.applySubst (inner : Subst) (outer : Subst) : Subst :=
  let innerList := inner.map.toList
  let outerMap := outer.map
  let map := Subst.applySubstHelper innerList outerMap
  {map := map : Subst}

---------------- modifyable state --------------------
structure InferState where
  ptAnnotationMap : Std.HashMap TypedRExprNode PhraseType := {}
  Counter : Nat := 0                                      -- counter for unique names

abbrev InferM := StateT InferState (Except String)

def getFreshAccessIdentifier (name : String := "tmp") : InferM String := do
  let cstate : InferState ← get
  set { cstate with Counter := cstate.Counter + 1 }
  return s!"{name}_{cstate.Counter}"

def ptAnnotationMap.put (node : TypedRExprNode) (pt : PhraseType) : InferM Unit :=
  modify (fun cstate => { cstate with ptAnnotationMap := cstate.ptAnnotationMap.insert node pt})

-------------- helper functions ----------------------------

def type (ty : RType) : InferM PhraseType := do
  match ty with
    | .data dt => let name ← getFreshAccessIdentifier
                  return PhraseType.expr dt (DAnnotation.identifier (Lean.Name.mkSimple name)) -- needs a unique name
    | .fn binderType body => let binderTyped  ← type binderType
                             let bodyTyped  ← type body
                             return (PhraseType.fn binderTyped bodyTyped)
    | .pi binderKind _ userName body => let bodyTyped  ← type body
                                        return PhraseType.pi (DKind.rise binderKind) userName bodyTyped


def funOutIsWrite (ePt : PhraseType) : Bool :=
  match ePt with
    | .pi _ _ body => funOutIsWrite body
    | .fn _ body => funOutIsWrite body
    | .expr _ a => match a with
                    | .identifier _ => false
                    | .write => true
                    | .read => false
    | _ => false

private def addsKernelParam (expr : RType) (kernelParamFun : Bool) : Bool :=
  match kernelParamFun with
    | true => match expr with
                | .pi _ _ _ _ => true
                | .fn _ _ => true
                | _ => false
    | false => false

private def subUnifyPhraseType (T1 T2 : PhraseType) : Option Subst :=
  match (T1, T2) with
    | (PhraseType.expr ldt la, PhraseType.expr rdt ra) =>
        if ldt == rdt
          then match (la, ra) with
                | (DAnnotation.identifier i, _) => some {map := Std.HashMap.ofList [(i,ra)] : Subst}
                | (_, DAnnotation.identifier i) => some {map := Std.HashMap.ofList [(i,la)] : Subst}
                | _ => none -- need to do type check le `<=` re
          else none

    | (PhraseType.pi _ luserName lbody, PhraseType.pi _ ruserName rbody) =>
        if luserName == ruserName
          then subUnifyPhraseType lbody rbody
          else none

    | (PhraseType.fn lbinderType lbody, PhraseType.fn rbinderType rbody) =>
        let val := subUnifyPhraseType lbinderType rbinderType
          match val with
            | some argSubst =>  let lout := Subst.applyPt argSubst lbody
                                let rout := Subst.applyPt argSubst rbody
                                let outSubst := subUnifyPhraseType lout rout
                                match outSubst with
                                  | some y => some (Subst.applySubst y argSubst)
                                  | none => none
            | none => none

    | _ => none

termination_by phraseTypeSize T1 + phraseTypeSize T2

-- private def subUnifyPhrase2 (T1 T2 : PhraseType) : Option Subst :=
--   match T1 with
--     | PhraseType.expr ldt la => match T2 with
--                         | PhraseType.expr rdt ra =>
--                             if ldt == rdt
--                               then match (la, ra) with
--                                     | (DAnnotation.identifier i, _) => some {map := Std.HashMap.ofList [(i,ra)] : Subst}
--                                     | (_, DAnnotation.identifier i) => some {map := Std.HashMap.ofList [(i,la)] : Subst}
--                                     | _ => none -- need to do type check le `<=` re
--                               else none
--                         | _ => none

--     | PhraseType.pi _ luserName lbody => match T2 with
--                                           | PhraseType.pi _ ruserName rbody =>
--                                             if luserName == ruserName
--                                               then subUnifyPhrase2 lbody rbody
--                                               else none
--                                           | _ => none

--     | PhraseType.fn lbinderType lbody => match T2 with
--                                           | PhraseType.fn rbinderType rbody =>
--                                               let val := subUnifyPhrase2 lbinderType rbinderType
--                                                 match val with
--                                                   | some argSubst =>  let lout := Subst.applyPt argSubst lbody
--                                                                       let rout := Subst.applyPt argSubst rbody
--                                                                       let outSubst := subUnifyPhrase2 lout rout
--                                                                       match outSubst with
--                                                                         | some y => some (Subst.applySubst y argSubst)
--                                                                         | none => none
--                                                   | none => none
--                                           | _ => none

--     | _ => none
--   termination_by phraseTypeSize T1 + phraseTypeSize T2

private def checkKindConsistency (rk : RKind) (dk : DKind) : Bool :=
  match dk with
    | .rise k => k == rk
    | _ => panic! s!"Kinds {rk} and {dk} not compatible"

def checkConsistency (rt : RType) (pt : PhraseType) : Unit :=
  match rt with
    | .fn inRt outRt => match pt with
                          | .fn inPt outPt => let _ := checkConsistency inRt inPt
                                              let _ := checkConsistency outRt outPt
                                              ()
                          | _ => panic! s!"Types {rt} and {pt} not compatible"
    | .pi kindRt _ _ outRt => match pt with
                                | .pi kindPt _ outPt => if checkKindConsistency kindRt kindPt
                                                          then panic! s!""
                                                          else checkConsistency outRt outPt
                                | _ => panic! s!"Types {rt} and {pt} not compatible"
    | .data _ => match pt with
                      | .expr _ _ => ()
                      | _ => panic! s!"Types {rt} and {pt} not compatible"

private def matchPrimitiveType (prim : Lean.Name) (primType : RType) : InferM PhraseType := do
  match prim.toString with
    | "mapSeq" | "mapSeqUnroll" | "iterateStream" => match primType with
                                                      | .fn (RType.fn (RType.data s) (RType.data t)) (RType.fn (RType.data (RData.array n _)) (RType.data (RData.array _ _))) =>
                                                              return (PhraseType.fn (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t DAnnotation.write)) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr (RData.array n t) DAnnotation.write)))
                                                      | _ => throw "error" -- terminate
    | "map" => match primType with
                | .fn (RType.fn (RType.data s) (RType.data t)) (RType.fn (RType.data (RData.array n _)) (RType.data (RData.array _ _))) =>
                        let name ← getFreshAccessIdentifier
                        let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                        return PhraseType.fn (PhraseType.fn (PhraseType.expr s ai) (PhraseType.expr t ai)) (PhraseType.fn (PhraseType.expr (RData.array n s) ai) (PhraseType.expr (RData.array n t) ai))
                | _ => throw "error" -- terminate
    | "mapFst" => match primType with
                  | .fn (RType.fn (RType.data dt1) (RType.data dt3)) (RType.fn (RType.data (RData.pair _ dt2)) (RType.data (RData.pair _ _))) =>
                          let name ← getFreshAccessIdentifier
                          let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                          return PhraseType.fn (PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.expr dt3 ai)) (PhraseType.fn (PhraseType.expr (RData.pair dt1 dt2) ai) (PhraseType.expr (RData.pair dt3 dt2) ai))
                  | _ => throw "error" -- terminate
    | "mapSnd" => match primType with
                  | .fn (RType.fn (RType.data dt2) (RType.data dt3)) (RType.fn (RType.data (RData.pair dt1 _)) (RType.data (RData.pair _ _))) =>
                          let name ← getFreshAccessIdentifier
                          let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                          return PhraseType.fn (PhraseType.fn (PhraseType.expr dt2 ai) (PhraseType.expr dt3 ai)) (PhraseType.fn (PhraseType.expr (RData.pair dt1 dt2) ai) (PhraseType.expr (RData.pair dt1 dt3) ai))
                  | _ => throw "error" -- terminate
    | "mapStream" => match primType with
                      | .fn (RType.fn (RType.data s) (RType.data t)) (RType.fn (RType.data (RData.array n _)) (RType.data (RData.array _ _))) =>
                              return PhraseType.fn (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t DAnnotation.write)) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr (RData.array n t) DAnnotation.read))
                      | _ => throw "error" -- terminate

    | "toMem" => match primType with
                  | .fn (RType.data t) (RType.data _) => return PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.expr t DAnnotation.read)
                  | _ => throw "error"

    | "join" | "transpose" | "asScalar" | "unzip" => match primType with
                                                      | .fn (RType.data dt1) (RType.data dt2) =>
                                                            let name ← getFreshAccessIdentifier
                                                            let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                                                            return PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.expr dt2 ai)
                                                      |_ => throw "error" -- terminate

    | "vectorFromScalar" | "neg" | "not" | "indexAsNat" | "fst" | "snd" | "cast" => match primType with
                                                                                      | .fn (RType.data dt1) (RType.data dt2) =>
                                                                                            return PhraseType.fn (PhraseType.expr dt1 DAnnotation.read) (PhraseType.expr dt2 DAnnotation.read)
                                                                                      | _ => throw "error" -- terminate

    | "concat" => match primType with
                    | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                          return PhraseType.fn (PhraseType.expr dt1 DAnnotation.write) (PhraseType.fn (PhraseType.expr dt2 DAnnotation.write) (PhraseType.expr dt3 DAnnotation.write))
                    | _ => throw "error" -- terminate

    | "rlet" => match primType with
                  | .fn (RType.data s) (RType.fn (RType.fn (RType.data _) (RType.data t)) (RType.data _)) =>
                        let name ← getFreshAccessIdentifier
                        let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                        return PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.fn (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t ai)) (PhraseType.expr t ai))
                  | _ => throw "error"

    | "split" | "asVector" | "asVectorAligned" => match primType with
                                                    | .fn _ _ => return PhraseType.comm --TODO look at it again
                                                    | _ => throw "error" -- terminate

    | "zip" | "makePair" => match primType with
                              | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                                  let name ← getFreshAccessIdentifier
                                  let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                                  return PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.fn (PhraseType.expr dt2 ai) (PhraseType.expr dt3 ai))
                              | _ => throw "error" -- terminate

    | "idx" | "add" | "sub" | "mult" | "div" | "gt" | "lt" | "equal" | "mod" | "gather" => match primType with
                                                                                            | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                                                                                                  return PhraseType.fn (PhraseType.expr dt1 DAnnotation.read) (PhraseType.fn (PhraseType.expr dt2 DAnnotation.read) (PhraseType.expr dt3 DAnnotation.read))
                                                                                            | _ => throw "error" --TODO: terminate

    | "scatter" => match primType with
                    | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                          return PhraseType.fn (PhraseType.expr dt1 DAnnotation.read) (PhraseType.fn (PhraseType.expr dt2 DAnnotation.write) (PhraseType.expr dt3 DAnnotation.write))
                    | _ => throw "error" -- terminate

    | "natAsIndex" | "take" | "drop" => match primType with
                                        | .fn _ _ => return PhraseType.comm --TODO look at it again
                                        | _ => throw "error" -- terminate

    | "reduceSeq" | "reduceSeqUnroll" => match primType with
                                          | .fn (RType.fn (RType.data t) (RType.fn (RType.data s) (RType.data _))) (RType.fn (RType.data _) (RType.fn (RType.data (RData.array n _)) (RType.data _))) =>
                                                  return PhraseType.fn
                                                          (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t DAnnotation.write)))
                                                          (PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr t DAnnotation.read)))
                                          | _ => throw "error" -- terminate

    | "scanSeq" => match primType with
                    | .fn (RType.fn (RType.data s) (RType.fn (RType.data t) (RType.data _))) (RType.fn (RType.data _) (RType.fn (RType.data (RData.array n _)) (RType.data _))) =>
                          return PhraseType.fn
                                  (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.expr t DAnnotation.write)))
                                  (PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr (RData.array n t) DAnnotation.write)))
                    | _ => throw "error"  -- terminate

    | "rotateValue" => match primType with
                        | .fn _ _ => return PhraseType.comm --TODO look at it again
                        | _ => throw "error" -- terminate

    | "circularBuffer" =>  match primType with
                            | .fn _ _ => return PhraseType.comm --TODO look at it again
                            | _ => throw "error" -- terminate

    | "slide" | "padClamp" =>  match primType with
                                | .fn _ _ => return PhraseType.comm --TODO look at it again
                                | _ => throw "error" -- terminate

    | "iterate" =>  match primType with
                      | .fn _ _ => return PhraseType.comm --TODO look at it again
                      | _ => throw "error" -- terminate

    | "oclIterate" =>  match primType with
                        | .fn _ _ => return PhraseType.comm --TODO look at it again
                        | _ => throw "error" -- terminate

    | "select" => match primType with
                    | .fn (RType.data (RData.scalar RScalar.bool)) (RType.fn (RType.data t) (RType.fn (RType.data _) (RType.data _))) =>
                          return PhraseType.fn (PhraseType.expr (RData.scalar RScalar.bool) DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.expr t DAnnotation.read)))
                    | _ => throw "error"  -- terminate

    | "padEmpty" =>  match primType with
                      | .fn _ _ => return PhraseType.comm --TODO look at it again
                      | _ => throw "error" -- terminate

    | "padCst" =>  match primType with
                    | .fn _ _ => return PhraseType.comm --TODO look at it again
                    | _ => throw "error" -- terminate

    | "generate" => match primType with
                      | .fn (RType.fn (RType.data (RData.index n)) (RType.data t)) (RType.data (RData.array _ _)) =>
                            return PhraseType.fn (PhraseType.fn (PhraseType.expr (RData.index n) DAnnotation.read) (PhraseType.expr t DAnnotation.read)) (PhraseType.expr (RData.array n t) DAnnotation.read)
                      | _ => throw "error"  -- terminate

    | "reorder" => match primType with
                    | .fn _ _ => return PhraseType.comm --TODO look at it again
                    | _ => throw "error" -- terminate

    | _ => throw "error"  -- terminate


---------------- Infer functions ----------------------

mutual
private def inferPhraseTypesMonadic (e : TypedRExpr) (ctx : Context) (isKernelParamFun : Bool) : InferM (PhraseType × Subst) := do
  let (pt, s) ← inferPhraseTypesHelper e ctx isKernelParamFun
  if isKernelParamFun then
      match pt with
        | .expr dt  _ => match subUnifyPhraseType pt (PhraseType.expr dt DAnnotation.write) with
                          | some subst => return ((Subst.applyPt subst pt), (Subst.applySubst s subst))
                          | none => throw "The program does not specify how to write the result of the program into its output" --panic! "This should never happen"
        | _ => return (pt, s)
  else return (pt, s)


private def inferPhraseTypesHelper (e : TypedRExpr) (ctx : Context) (isKernelParamFun : Bool) : InferM (PhraseType × Subst) := do
  let node := e.node
  match node with
    | .bvar deBruijnIndex userName =>
        let val := ctx.get? e
        match val with
          | some pt =>  ptAnnotationMap.put node pt
                        return (pt, {map := {} : Subst})
          | none => throw "this should never happen" --panic! "This should never happen"
    | .const userName => inferPrimitive node e.type userName
    | .lit val =>
        let lpt := PhraseType.expr (exprTypeToDataType e.type) DAnnotation.read -- take a look at again
        ptAnnotationMap.put node lpt
        return (lpt, {map := {} : Subst})
    | .app fn arg => inferApp node fn arg ctx (addsKernelParam e.type isKernelParamFun)
    | .depapp fn arg => inferDepApp node fn arg ctx isKernelParamFun
    | .lam binderName binderType body => inferLambda node binderName binderType body PhraseType.comm ctx isKernelParamFun
    | .deplam binderName binderKind body => inferDepLambda node binderName binderKind body ctx isKernelParamFun
    | _ => throw "fvars and mvars should not be here anymore "



----- infer Primitive PhraseTypes -------------------

private def inferPrimitive (primNode : TypedRExprNode) (primType : RType) (prim : Lean.Name) : InferM (PhraseType × Subst) := do
  let primitiveType ← matchPrimitiveType prim primType
  let _ := checkConsistency primType primitiveType
  ptAnnotationMap.put primNode primitiveType
  return (primitiveType, {map := {} : Subst})





--- infer application PhraseTypes -------------------

private def inferApp (app : TypedRExprNode) (fn arg : TypedRExpr) (ctx : Context) (isKernelParamFun : Bool ) : InferM (PhraseType × Subst) := do
  let (fType, fSubst) ← inferPhraseTypesMonadic fn ctx isKernelParamFun
  let (argType, argSubst) ← inferPhraseTypesMonadic arg ctx isKernelParamFun
  let argSubstFType := Subst.applyPt argSubst fType
  match argSubstFType with
    | .fn binderType body => let subst  ← match subUnifyPhraseType argType binderType with -- in scala asInstanceOf so not correkt here?
                                | some y => pure y
                                | none => throw "subUnifyPhraseType failed"
                             let appType := Subst.applyPt subst body
                             let resSubst := Subst.applySubst subst (Subst.applySubst argSubst fSubst)
                             ptAnnotationMap.put app appType
                             return (appType, resSubst)
    | _ => throw s!"{fn} is no function type"



--- infer dependent application PhraseTypes -------------------

private def inferDepApp (depApp : TypedRExprNode) (fn : TypedRExpr) (arg : RWrapper) (ctx : Context) (isKernelParamFun : Bool ) : InferM (PhraseType × Subst) := do
  let (fType, fSubst) ← inferPhraseTypesMonadic fn ctx isKernelParamFun
  let depAppType := match arg with
                          | .nat n => liftDependentFunctionNat fType n
                          | .data dt => liftDependentFunctionData fType dt
                          | .type t => return (PhraseType.comm, {map := {} : Subst}) -- what should i do?
  ptAnnotationMap.put depApp depAppType
  return (depAppType, fSubst)




--- infer Lambda PhraseTypes -------------------

private def inferLambda (lam : TypedRExprNode) (binderName : Lean.Name) (binderType : RType) (body : TypedRExpr) (Ptype : PhraseType) (ctx : Context) (isKernelParamFun : Bool) : InferM (PhraseType × Subst) := do
  let xType ← if isKernelParamFun
                  then pure (PhraseType.expr (exprTypeToDataType binderType) DAnnotation.read)
                  else type binderType
  let node :=  TypedRExprNode.bvar 0 binderName
  let ctxWithX := ctx.insert {node := node, type := binderType : TypedRExpr}  xType
  let (eType, eSubst) ← inferPhraseTypesMonadic body ctxWithX isKernelParamFun
  let lambdaType := PhraseType.fn (Subst.applyPt eSubst xType) eType
  ptAnnotationMap.put node xType
  ptAnnotationMap.put lam lambdaType
  return (lambdaType, eSubst)



--- infer dependent Lambda Phrasetypes -------------------

private def inferDepLambda (depLam : TypedRExprNode) (binderName : Lean.Name) (binderKind : RKind) (body : TypedRExpr) (ctx : Context) (isKernelParamFun : Bool) : InferM (PhraseType × Subst) := do
  let (bodyType, bodySubst) ← inferPhraseTypesMonadic body ctx isKernelParamFun
  let depLamType := PhraseType.pi (DKind.rise binderKind) binderName bodyType
  ptAnnotationMap.put depLam depLamType
  return (depLamType, bodySubst)

end

--- outer call
def inferPhraseTypes (e : TypedRExpr) (ctx : Context) (isKernelParamFun : Bool) : (PhraseType × Subst) :=
  let result := (inferPhraseTypesMonadic e ctx isKernelParamFun).run {Counter := 0, ptAnnotationMap := {}}
  match result with
    | .ok ((pt, s), _) => (pt, s)
    | .error msg => (PhraseType.comm, {map := {} : Subst}) --- want it to fail
