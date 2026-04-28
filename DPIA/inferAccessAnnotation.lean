import DPIA.Substitutions
import DPIA.Basic
import DPIA.TypeCheck

-- helper type
private abbrev SubstMap := Std.HashMap Lean.Name DAnnotation
private abbrev FunctionContext := Std.HashMap (Lean.Name × Nat) PhraseType


def printFunctionContext (ctx : List ((Lean.Name × Nat) × PhraseType)) : String :=
  match ctx with
    | [] => ""
    | (key, val) :: ys => s!"({key},{val}) \n\n" ++ printFunctionContext ys


---------------- substType -----------------
structure Subst where
  map : SubstMap

partial def applySubstToRExprHelper (rPt : RExprPt) (name : Lean.Name) (val : DAnnotation) : RExprPt :=
  let sType := substituteAnnotationPt rPt.type name val
  match rPt.node with
    | .bvar .. => {node := rPt.node, type := sType}
    | .const _ => {node := rPt.node, type := sType}
    | .lit _ => {node := rPt.node, type := sType}
    | .app fn arg =>  let sFn := applySubstToRExprHelper fn name val
                      let sArg := applySubstToRExprHelper arg name val
                      {node := .app sFn sArg, type := sType}
    | .depapp fn arg => let sFn := applySubstToRExprHelper fn name val
                        {node := .depapp sFn arg, type := sType}
    | .lam binderName binderType body =>  let sBody := applySubstToRExprHelper body name val
                                          {node := .lam binderName binderType sBody, type := sType}
    | .deplam binderName binderKind body => let sBody := applySubstToRExprHelper body name val
                                            {node := .deplam binderName binderKind sBody, type := sType}

def applySubstToRExpr (subst : Subst) (rPt : RExprPt) : RExprPt :=
  subst.map.fold (fun acc key value => applySubstToRExprHelper acc key value) (init := rPt)

def applySubstToPt (subst : Subst) (pt : PhraseType) : PhraseType :=
  subst.map.fold (fun acc key value => substituteAnnotationPt acc key value) (init := pt)

def applySubstToSubstHelper (inner : List (Lean.Name × DAnnotation)) (outer : SubstMap) : SubstMap :=
  match inner with
    | [] => outer
    | (key, value) :: ys => let val := outer.get? key
                            match val with
                              | some y => if y == value then applySubstToSubstHelper ys outer
                                            else panic! s!"Unexpectedly assigning var {key} multiple times."
                              | none => let new := outer.insert key value
                                        applySubstToSubstHelper ys new

def applySubstToSubst (inner : Subst) (outer : Subst) : Subst :=
  let innerList := inner.map.toList
  let outerMap := outer.map
  {map := applySubstToSubstHelper innerList outerMap}

def traverseList (pt : PhraseType) (outer : List (Lean.Name × DAnnotation)) : PhraseType :=
  match outer with
    | [] => pt
    | (key, value) :: ys => let SubstPt := substituteAnnotationPt pt key value
                            traverseList SubstPt ys

def applySubstToMap (inner : FunctionContext) (outer : Subst)  : FunctionContext :=
  let outerList := outer.map.toList
  inner.fold  (fun acc key value => let pt := traverseList value outerList
                                    acc.insert key pt)
              (init := Std.HashMap.emptyWithCapacity)

---------------- modifyable state --------------------
structure InferState where
  Counter : Nat := 0                                      -- counter for unique names
  depth : Nat := 0

abbrev InferM := StateT InferState (Except String)        -- for exeptions using throw

def getFreshAccessIdentifier (name : String := "tmp") : InferM Lean.Name := do
  let cstate : InferState ← get
  set { cstate with Counter := cstate.Counter + 1}
  return Lean.Name.mkSimple s!"{name}_{cstate.Counter}"


def insertInCtx (ctx : FunctionContext) (name : Lean.Name) (type : PhraseType) : InferM FunctionContext := do
  let cstate : InferState ← get
  let newCtx := ctx.insert (name, cstate.depth) type
  set { cstate with depth := cstate.depth + 1}
  return newCtx

def getRec (idx depth : Nat) (name : Lean.Name) (ctx : List ((Lean.Name × Nat) × PhraseType)) : InferM PhraseType := do
  match ctx with
    | [] => throw s!"cannot find identifier {name}@{idx} at depth {depth}"
    | ((idf, d), type) :: ys => if name.toString == idf.toString && (depth-idx) - d == 0 then return type
                                else getRec idx depth name ys

def getFromCtx (idx : Nat) (name : Lean.Name) (ctx : FunctionContext) : InferM PhraseType := do
  let cstate : InferState ← get
  if cstate.depth == 0 then throw s!"cannot find identifier {name}@{idx} because there are no functions yet\n {printFunctionContext ctx.toList}"
  else getRec idx (cstate.depth-1) name ctx.toList

-------------- helper functions ----------------------------

def type (ty : RType) : InferM PhraseType := do
  match ty with
    | .data dt => return .expr dt (.identifier (← getFreshAccessIdentifier))
    | .fn binderType body => return .fn (← type binderType) (← type body)
    | .pi binderKind _ userName body => return .pi (.rise binderKind) userName (← type body)


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

partial def subUnifyPhraseType (subType superType : PhraseType) : Option Subst :=
  match (subType, superType) with
    | (PhraseType.expr ldt la, PhraseType.expr rdt ra) =>
        if ldt == rdt
          then match (la, ra) with
                | (.identifier i, _) => some {map := Std.HashMap.ofList [(i,ra)] : Subst}
                | (_, .identifier i) => some {map := Std.HashMap.ofList [(i,la)] : Subst}
                | _ => if (subTypeCheck subType superType) then some {map := {} : Subst}
                        else none
          else none
    | (.pi _ luserName lbody, .pi _ ruserName rbody) =>
        if luserName == ruserName
          then subUnifyPhraseType lbody rbody
          else none
    | (.fn lBinderType lBody, .fn rBinderType rBody) =>
        let val := subUnifyPhraseType lBinderType rBinderType
          match val with
            | some argSubst =>  let lout := applySubstToPt argSubst lBody
                                let rout := applySubstToPt argSubst rBody
                                let outSubst := subUnifyPhraseType lout rout
                                match outSubst with
                                  | some y => some (applySubstToSubst y argSubst)
                                  | none => none
            | none => none
    | _ => none

private def checkKindConsistency (rk : RKind) (dk : DKind) : Bool :=
  match dk with
    | .rise k => k != rk
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
                                                      | .fn (.fn (.data s) (.data t)) (.fn (.data (.array n _)) (.data (.array _ _))) =>
                                                            return (.fn (.fn  (.expr s .read) (.expr t .write))
                                                                        (.fn  (.expr (.array n s) .read) (.expr (.array n t) .write)))
                                                      | _ => throw s!"{primType} is no match for mapSeq / mapSeqUnroll / iterateStream" -- terminate
    | "map" => match primType with
                | .fn (.fn (.data s) (.data t))  (.fn   (.data (.array n _)) (.data (.array _ _))) =>
                      let ai := .identifier (← getFreshAccessIdentifier)
                      return .fn (.fn (.expr s ai) (.expr t ai))
                                 (.fn (.expr (.array n s) ai) (.expr (.array n t) ai))
                | _ => throw s!"{primType} is no match for map"
    | "mapFst" => match primType with
                  | .fn (.fn (.data dt1) (.data dt3)) (.fn (.data (.pair _ dt2)) (.data (.pair _ _))) =>
                        let ai := DAnnotation.identifier (← getFreshAccessIdentifier)
                          return .fn (.fn (.expr dt1 ai) (.expr dt3 ai))
                                     (.fn (.expr (.pair dt1 dt2) ai) (.expr (.pair dt3 dt2) ai))
                  | _ => throw s!"{primType} is no match for mapFst"
    | "mapSnd" => match primType with
                  | .fn (.fn (.data dt2) (.data dt3)) (.fn (.data (.pair dt1 _)) (.data (.pair _ _))) =>
                          let ai := (DAnnotation.identifier (← getFreshAccessIdentifier))
                          return .fn (.fn (.expr dt2 ai) (.expr dt3 ai)) (.fn (.expr (.pair dt1 dt2) ai) (.expr (.pair dt1 dt3) ai))
                  | _ => throw s!"{primType} is no match for mapSnd"
    | "mapStream" => match primType with
                      | .fn (.fn (.data s) (.data t)) (.fn (.data (.array n _)) (.data (.array _ _))) =>
                              return .fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n s) .read) (.expr (.array n t) .read))
                      | _ => throw s!"{primType} is no match for mapStream"
    | "toMem" => match primType with
                  | .fn (.data t) (.data _) => return .fn (.expr t .write) (.expr t .read)
                  | _ => throw s!"{primType} is no match for toMem"
    | "join" | "transpose" | "asScalar" | "unzip" => match primType with
                                                      | .fn (.data dt1) (.data dt2) => let ai := (DAnnotation.identifier (← getFreshAccessIdentifier))
                                                                                       return .fn (.expr dt1 ai) (.expr dt2 ai)
                                                      |_ => throw s!"{primType} is no match for join / transpose / asScalar / unzip"
    | "vectorFromScalar" | "neg" | "not" | "indexAsNat" | "fst" | "snd" | "cast" => match primType with
                                                                                      | .fn (.data dt1) (.data dt2) =>
                                                                                            return .fn (.expr dt1 .read) (.expr dt2 .read)
                                                                                      | _ => throw s!"{primType} is no match for vectorFromScalar / neg / not / indexAsnat / fst / snd / cast"
    | "concat" => match primType with
                    | .fn (.data dt1) (.fn (.data dt2) (.data dt3)) => return .fn (.expr dt1 .write) (.fn (.expr dt2 .write) (.expr dt3 .write))
                    | _ => throw s!"{primType} is no match for concat"
    | "rlet" => match primType with
                  | .fn (.data s) (.fn (.fn (.data _) (.data t)) (.data _)) =>
                        let ai := (DAnnotation.identifier (← getFreshAccessIdentifier))
                        return .fn (.expr s .read) (.fn (.fn (.expr s .read) (.expr t ai)) (.expr t ai))
                  | _ => throw s!"{primType} is no match for rlet"
    | "split" | "asVector" | "asVectorAligned" => match primType with
                                                    | .pi .nat _ userName (.fn (.data dt1) (.data dt2)) => let ai := (DAnnotation.identifier (← getFreshAccessIdentifier))
                                                                                                           return .pi (.rise .nat) userName (.fn (.expr dt1 ai) (.expr dt2 ai))
                                                    | _ => throw s!"{primType} is no match for split / asVector / asVector Aligned"
    | "zip" | "makePair" => match primType with
                              | .fn (.data dt1) (.fn (.data dt2) (.data dt3)) =>  let ai := (DAnnotation.identifier (← getFreshAccessIdentifier))
                                                                                  return .fn (.expr dt1 ai) (.fn (.expr dt2 ai) (.expr dt3 ai))
                              | _ => throw s!"{primType} is no match for zip / makPair"
    | "idx" | "add" | "sub" | "mul" | "div" | "gt" | "lt" | "equal" | "mod" | "gather" => match primType with
                                                                                            | .fn (.data dt1) (.fn (.data dt2) (.data dt3)) => return .fn (.expr dt1 .read) (.fn  (.expr dt2 .read) (.expr dt3 .read))
                                                                                            | _ => throw s!"{primType} is no match for idx / add / sub / mult / div / gt / lt / equal / mod / gather"
    | "scatter" => match primType with
                    | .fn (.data dt1) (.fn (.data dt2) (.data dt3)) => return .fn (.expr dt1 .read) (.fn (.expr dt2 .write) (.expr dt3 .write))
                    | _ => throw s!"{primType} is no match for scatter"
    | "natAsIndex" | "take" | "drop" => match primType with
                                        | .pi .nat _ userName (.fn (.data dt1) (.data dt2)) => return .pi (.rise .nat) userName (.fn (.expr dt1 .read) (.expr dt2 .read))
                                        | _ => throw s!"{primType} is no match for natAsIndex"
    | "reduceSeq" | "reduceSeqUnroll" => match primType with
                                          | .fn (.fn (.data t) (.fn (.data s) (.data _))) (.fn (.data _) (.fn (.data (.array n _)) (.data _))) =>
                                                  return .fn (.fn (.expr t .read) (.fn (.expr s .read) (.expr t .write)))
                                                             (.fn (.expr t .write) (.fn (.expr (.array n s) .read) (.expr t .read)))
                                          | _ => throw s!"{primType} is no match for reduceSeq / reduceSeqUnroll"
    | "scanSeq" => match primType with
                    | .fn (.fn (.data s) (.fn (.data t) (.data _))) (.fn (.data _) (.fn (.data (.array n _)) (.data _))) =>
                          return .fn (.fn (.expr s .read) (.fn (.expr t .read) (.expr t .write)))
                                     (.fn (.expr t .write) (.fn (.expr (.array n s) .read) (.expr (.array n t) .write)))
                    | _ => throw s!"{primType} is no match for scanSeq"
    | "rotateValue" => match primType with
                        | .pi .nat _ sz (.fn (.fn (.data s) (.data _)) (.fn (.data (.array nIn dtIn)) (.data (.array nOut dtOut)))) =>
                            return .pi (.rise .nat) sz (.fn (.fn (.expr s .read) (.expr s .write)) (.fn (.expr (.array nIn dtIn) .read) (.expr (.array nOut dtOut) .read)))
                        | _ => throw s!"{primType} is no match for rotateValue"
    | "circularBuffer" =>  match primType with
                            | .pi .nat _ alloc (.pi .nat _ sz
                                  (.fn (.fn (.data s) (.data _))
                                       (.fn (.data (.array nIn dtIn)) (.data (.array nOut dtOut))))) =>
                               return .pi (.rise .nat) alloc (.pi (.rise .nat) sz
                                          (.fn (.fn (.expr s .read) (.expr s .write))
                                               (.fn (.expr (.array nIn dtIn) .read) (.expr (.array nOut dtOut) .read))))
                            | _ => throw s!"{primType} is no match for circularBuffer"
    | "slide" | "padClamp" =>  match primType with
                                | .pi .nat _ sz (.pi .nat _ sp (.fn (.data dt1) (.data dt2))) =>
                                      return .pi (.rise .nat) sz (.pi (.rise .nat) sp (.fn (.expr dt1 .read) (.expr dt2 .read)))
                                | _ => throw s!"{primType} is no match for slide / padClamp"

    | "iterate" =>  match primType with
                      | .pi .nat _ k
                            (.fn (.pi .nat _ l (.fn (.data (.array n1 at1)) (.data (.array n2 at2))))
                                 (.fn (.data (.array n3 at3)) (.data (.array n4 at4)))) =>
                          return .pi (.rise .nat) k
                                     (.fn (.pi (.rise .nat) l (.fn (.expr (.array n1 at1) .read) (.expr (.array n2 at2) .write)))
                                          (.fn (.expr (.array n3 at3) .read) (.expr (.array n4 at4) .write)))
                      | _ => throw s!"{primType} is no match for iterate"
    | "oclIterate" =>  match primType with
                        | .fn _ _ => return PhraseType.comm --TODO look at it again -> no address
                        | _ => throw s!"{primType} is no match for oclIterate"
    | "select" => match primType with
                    | .fn (.data (.scalar .bool)) (.fn (.data t) (.fn (.data _) (.data _))) =>
                          return .fn (.expr (.scalar .bool) .read) (.fn (.expr t .read) (.fn (.expr t .read) (.expr t .read)))
                    | _ => throw s!"{primType} is no match for select"
    | "padEmpty" =>  match primType with
                      | .pi .nat _ r (.fn (.data (.array n t)) (.data (.array _ _))) =>
                          return .pi (.rise .nat) r  (.fn (.expr (.array n t) .write) (.expr (.array (.plus n (.bvar 0 r)) t) .write))
                      | _ => throw s!"{primType} is no match for padEmpty"
    | "padCst" =>  match primType with
                    | .pi .nat _ l (.pi .nat _ q
                         (.fn (.data t) (.fn (.data (.array n _)) (.data (.array _ _))))) =>
                        return .pi (.rise .nat) l (.pi (.rise .nat) q
                                   (.fn (.expr t .read) (.fn (.expr (.array n t) .read) (.expr (.array (.plus (.bvar 1 l) (.plus (.bvar 0 q) n)) t) .read))))
                    | _ => throw s!"{primType} is no match for padCast"
    | "generate" => match primType with
                      | .fn (.fn (.data (.index n)) (.data t)) (.data (.array _ _)) =>
                            return .fn (.fn (.expr (.index n) .read) (.expr t .read)) (.expr (.array n t) .read)
                      | _ => throw "generate"
    | _ => throw s!"no match for {prim}"


---------------- Infer functions ----------------------

mutual
partial def inferPhraseTypes (e : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (RExprPt × Subst) := do
  let (rPt, s) ← inferPhraseTypesHelper e ctx isKernelParamFun
  if isKernelParamFun then
      match rPt.type with
        | .expr dt  _ => match subUnifyPhraseType rPt.type (PhraseType.expr dt DAnnotation.write) with
                          | some subst => return (applySubstToRExpr subst rPt, applySubstToSubst s subst)
                          | none => throw "The program does not specify how to write the result of the program into its output"
        | _ => return (rPt, s)
  else return (rPt, s)



partial def inferPhraseTypesHelper (e : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (RExprPt × Subst) := do
  let node := e.node
  match node with
    | .bvar idx name =>
        let val ← getFromCtx idx name ctx
        return ({node := .bvar idx name, type := val : RExprPt},{map := {} : Subst})
    | .const userName => inferPrimitive e.type userName
    | .lit v => let lpt := PhraseType.expr (assertDataType e.type) DAnnotation.read
                return ({node := .lit v, type := lpt : RExprPt}, {map := {} : Subst})
    | .app fn arg => inferApp fn arg ctx (addsKernelParam e.type isKernelParamFun)
    | .depapp fn arg => inferDepApp fn arg ctx isKernelParamFun
    | .lam binderName binderType body => let inT := assertFunctionType e.type
                                         inferLambda binderName binderType body inT ctx isKernelParamFun
    | .deplam binderName binderKind body => inferDepLambda binderName binderKind body ctx isKernelParamFun



----- infer Primitive PhraseTypes -------------------

partial def inferPrimitive (primType : RType) (prim : Lean.Name) : InferM (RExprPt × Subst) := do
  let primitiveType ← matchPrimitiveType prim primType
  let _ := checkConsistency primType primitiveType
  return ({node := .const prim, type := primitiveType : RExprPt}, {map := {} : Subst})


--- infer application PhraseTypes -------------------

partial def inferApp (fn arg : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool ) : InferM (RExprPt × Subst) := do
  let (fExpr, fSubst) ← inferPhraseTypes fn ctx isKernelParamFun
  let (argExpr, argSubst) ← inferPhraseTypes arg (applySubstToMap ctx fSubst) isKernelParamFun
  let argSubstFExpr := applySubstToRExpr argSubst fExpr
  match argSubstFExpr.type with
    | .fn binderType body => let subst  ← match subUnifyPhraseType argExpr.type binderType with
                                | some y => pure  y
                                | none => throw s!"subUnifyPhraseType failed for the argument type: {argExpr.type} \n and the binder type {binderType}"
                             let appType := applySubstToPt subst body
                             let resSubst := applySubstToSubst subst (applySubstToSubst argSubst fSubst)
                             return ({node := .app argSubstFExpr argExpr, type := appType : RExprPt}, resSubst)
    | _ => throw s!"{fn} is no function type"

partial def inferDepApp (fn : RExpr) (arg : RWrapper) (ctx : FunctionContext) (isKernelParamFun : Bool ) : InferM (RExprPt × Subst) := do
  let (fExpr, fSubst) ← inferPhraseTypes fn ctx isKernelParamFun
  let depAppType ← match (arg, fExpr.type) with
                          | (.nat n, .pi (.rise .nat) userName body) => pure (substituteNatInPhraseType n userName body)
                          | (.data dt, .pi (.rise .data) userName body)  => pure (substituteDataInPhraseType dt userName body)
                          | (_ , _) => throw s!"the argument does not match with the function type " --- access identifier is missing yet

  return ({type := depAppType, node := .depapp fExpr arg : RExprPt}, fSubst)


--- infer Lambda PhraseTypes -------------------

partial def inferLambda (binderName : Lean.Name) (binderType : RType) (body : RExpr) (inT : RType) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (RExprPt × Subst) := do
  let xType ← if isKernelParamFun
                  then pure (PhraseType.expr (assertDataType inT) .read)
                  else type binderType
  let ctxWithX ← insertInCtx ctx binderName xType
  let (bodyExpr, bodySubst) ← inferPhraseTypes body ctxWithX isKernelParamFun
  let lambdaType := PhraseType.fn (applySubstToPt bodySubst xType) bodyExpr.type

  -- set depth like before
  let cstate ← get
  set { cstate with depth := cstate.depth - 1}

  return ({type := lambdaType, node :=.lam binderName binderType bodyExpr : RExprPt}, bodySubst)



--- infer dependent Lambda Phrasetypes -------------------

partial def inferDepLambda (binderName : Lean.Name) (binderKind : RKind) (body : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (RExprPt × Subst) := do
  let (bodyExpr, bodySubst) ← inferPhraseTypes body ctx isKernelParamFun
  let depLamType := PhraseType.pi (DKind.rise binderKind) binderName bodyExpr.type
  return ({type := depLamType, node := .deplam binderName binderKind bodyExpr :RExprPt}, bodySubst)

end

----- outer call for infer Access --------------

def inferAccess (expr : RExpr) : RExprPt :=
    let result := (inferPhraseTypes expr {} true).run {Counter := 0, depth := 0}
    match result with
        | .ok ((rPt, subst), _) => applySubstToRExpr subst rPt
        | .error msg => panic! s!"error ocurred during inferAccess: \n {msg}"
