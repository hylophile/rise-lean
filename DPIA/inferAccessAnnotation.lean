import DPIA.Substitutions
import DPIA.Basic
import DPIA.TypeCheck

-- helper type
private abbrev Context := Std.HashMap RExpr PhraseType
private abbrev SubstMap := Std.HashMap Lean.Name DAnnotation
private abbrev FunctionContext := Std.HashMap (Lean.Name × Nat) PhraseType


def printContext (ctx : List ((Lean.Name × Nat) × PhraseType)) : String :=
  match ctx with
    | [] => ""
    | (key, val) :: ys => s!"({key},{val}) \n\n" ++ printContext ys


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

def traverseList (pt : PhraseType) (outer : List (Lean.Name × DAnnotation)) : PhraseType :=
  match outer with
    | [] => pt
    | (key, value) :: ys => let SubstPt := substituteAnnotationPt pt key value
                            traverseList SubstPt ys

def Subst.applyMap (inner : Context) (outer : Subst)  : Context :=
  let outerList := outer.map.toList
  inner.fold
    (fun acc key value =>
     let pt := traverseList value outerList
     acc.insert key pt)
    (init := Std.HashMap.emptyWithCapacity)

def printSubst (subst : List (Lean.Name × DAnnotation)) : String :=
    match subst with
    | [] => ""
    | (key, val) :: ys => s!"({key},{val}) \n\n" ++ printSubst ys

---------------- modifyable state --------------------
structure InferState where
  ptAnnotationMap : Context := {}
  Counter : Nat := 0                                      -- counter for unique names
  depth : Nat := 0

abbrev InferM := StateT InferState (Except String)

def getFreshAccessIdentifier (name : String := "tmp") : InferM String := do
  let cstate : InferState ← get
  set { cstate with Counter := cstate.Counter + 1}
  return s!"{name}_{cstate.Counter}"

def ptAnnotationMap.put (node : RExpr) (pt : PhraseType) : InferM Unit :=
  modify (fun cstate => { cstate with ptAnnotationMap := cstate.ptAnnotationMap.insert node pt})


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
  if cstate.depth == 0 then throw s!"cannot find identifier {name}@{idx} because there are no functions yet\n {printContext ctx.toList}"
  getRec idx (cstate.depth-1) name ctx.toList

-------------- helper functions ----------------------------

def mkApp (fNode argNode : RExprNodePt) (fType argType : PhraseType) : RExprNodePt :=
    .app {node := fNode, type := fType : RExprPt} {node:= argNode, type := argType: RExprPt}

def mkDepApp (fNode : RExprNodePt) (fType : PhraseType) (arg : RWrapper) : RExprNodePt :=
    .depapp {node := fNode, type := fType} arg

def mkLam (name : Name) (binderType : RType) (fNode : RExprNodePt) (fType : PhraseType) : RExprNodePt :=
    .lam name binderType {node := fNode, type := fType : RExprPt}

def mkDepLam (name : Name) (kind : RKind) (fNode : RExprNodePt) (fType : PhraseType) : RExprNodePt :=
    .deplam name kind {node := fNode, type := fType : RExprPt}

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

partial def subUnifyPhraseType (subType superType : PhraseType) : Option Subst :=
  match (subType, superType) with
    | (PhraseType.expr ldt la, PhraseType.expr rdt ra) =>
        if ldt == rdt
          then match (la, ra) with
                | (DAnnotation.identifier i, _) => some {map := Std.HashMap.ofList [(i,ra)] : Subst}
                | (_, DAnnotation.identifier i) => some {map := Std.HashMap.ofList [(i,la)] : Subst}
                | _ => if (subTypeCheck subType superType) then some {map := {} : Subst}
                        else none
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

--termination_by phraseTypeSize T1 + phraseTypeSize T2

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
                                                      | .fn (RType.fn   (RType.data s)
                                                                        (RType.data t))
                                                            (RType.fn   (RType.data (RData.array n _))
                                                                        (RType.data (RData.array _ _))) =>
                                                            return (PhraseType.fn   (PhraseType.fn  (PhraseType.expr s DAnnotation.read)
                                                                                                    (PhraseType.expr t DAnnotation.write))
                                                                                    (PhraseType.fn  (PhraseType.expr (RData.array n s) DAnnotation.read)
                                                                                                    (PhraseType.expr (RData.array n t) DAnnotation.write)))
                                                      | _ => throw s!"{primType} is no match for mapSeq / mapSeqUnroll / iterateStream" -- terminate
    | "map" => match primType with
                | .fn   (RType.fn (RType.data s) (RType.data t))
                        (RType.fn   (RType.data (RData.array n _))
                                    (RType.data (RData.array _ _))) =>
                        let name ← getFreshAccessIdentifier
                        let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                        return PhraseType.fn (PhraseType.fn (PhraseType.expr s ai) (PhraseType.expr t ai)) (PhraseType.fn (PhraseType.expr (RData.array n s) ai) (PhraseType.expr (RData.array n t) ai))
                | _ => throw s!"{primType} is no match for map" -- terminate
    | "mapFst" => match primType with
                  | .fn (RType.fn (RType.data dt1) (RType.data dt3)) (RType.fn (RType.data (RData.pair _ dt2)) (RType.data (RData.pair _ _))) =>
                          let name ← getFreshAccessIdentifier
                          let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                          return PhraseType.fn (PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.expr dt3 ai)) (PhraseType.fn (PhraseType.expr (RData.pair dt1 dt2) ai) (PhraseType.expr (RData.pair dt3 dt2) ai))
                  | _ => throw s!"{primType} is no match for mapFst" -- terminate
    | "mapSnd" => match primType with
                  | .fn (RType.fn (RType.data dt2) (RType.data dt3)) (RType.fn (RType.data (RData.pair dt1 _)) (RType.data (RData.pair _ _))) =>
                          let name ← getFreshAccessIdentifier
                          let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                          return PhraseType.fn (PhraseType.fn (PhraseType.expr dt2 ai) (PhraseType.expr dt3 ai)) (PhraseType.fn (PhraseType.expr (RData.pair dt1 dt2) ai) (PhraseType.expr (RData.pair dt1 dt3) ai))
                  | _ => throw s!"{primType} is no match for mapSnd" -- terminate
    | "mapStream" => match primType with
                      | .fn (RType.fn (RType.data s) (RType.data t)) (RType.fn (RType.data (RData.array n _)) (RType.data (RData.array _ _))) =>
                              return PhraseType.fn (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t DAnnotation.write)) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr (RData.array n t) DAnnotation.read))
                      | _ => throw s!"{primType} is no match for mapStream" -- terminate

    | "toMem" => match primType with
                  | .fn (RType.data t) (RType.data _) => return PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.expr t DAnnotation.read)
                  | _ => throw s!"{primType} is no match for toMem"

    | "join" | "transpose" | "asScalar" | "unzip" => match primType with
                                                      | .fn (RType.data dt1) (RType.data dt2) =>
                                                            let name ← getFreshAccessIdentifier
                                                            let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                                                            return PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.expr dt2 ai)
                                                      |_ => throw s!"{primType} is no match for join / transpose / asScalar / unzip" -- terminate

    | "vectorFromScalar" | "neg" | "not" | "indexAsNat" | "fst" | "snd" | "cast" => match primType with
                                                                                      | .fn (RType.data dt1) (RType.data dt2) =>
                                                                                            return PhraseType.fn (PhraseType.expr dt1 DAnnotation.read) (PhraseType.expr dt2 DAnnotation.read)
                                                                                      | _ => throw s!"{primType} is no match for vectorFromScalar / neg / not / indexAsnat / fst / snd / cast" -- terminate

    | "concat" => match primType with
                    | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                          return PhraseType.fn (PhraseType.expr dt1 DAnnotation.write) (PhraseType.fn (PhraseType.expr dt2 DAnnotation.write) (PhraseType.expr dt3 DAnnotation.write))
                    | _ => throw s!"{primType} is no match for concat" -- terminate

    | "rlet" => match primType with
                  | .fn (RType.data s) (RType.fn (RType.fn (RType.data _) (RType.data t)) (RType.data _)) =>
                        let name ← getFreshAccessIdentifier
                        let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                        return PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.fn (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t ai)) (PhraseType.expr t ai))
                  | _ => throw s!"{primType} is no match for rlet"

    | "split" | "asVector" | "asVectorAligned" => match primType with
                                                    | .pi .nat _ userName (.fn (.data dt1) (.data dt2)) => let name ← getFreshAccessIdentifier
                                                                                                           let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                                                                                                           return PhraseType.pi (.rise .nat) userName (.fn (.expr dt1 ai) (.expr dt2 ai))
                                                    | _ => throw s!"{primType} is no match for split / asVector / asVector Aligned" -- terminate

    | "zip" | "makePair" => match primType with
                              | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                                  let name ← getFreshAccessIdentifier
                                  let ai := (DAnnotation.identifier (Lean.Name.mkSimple name))
                                  return PhraseType.fn (PhraseType.expr dt1 ai) (PhraseType.fn (PhraseType.expr dt2 ai) (PhraseType.expr dt3 ai))
                              | _ => throw s!"{primType} is no match for zip / makPair" -- terminate

    | "idx" | "add" | "sub" | "mul" | "div" | "gt" | "lt" | "equal" | "mod" | "gather" => match primType with
                                                                                            | .fn   (RType.data dt1)
                                                                                                    (RType.fn   (RType.data dt2)
                                                                                                                (RType.data dt3)) =>
                                                                                                  return PhraseType.fn  (PhraseType.expr dt1 DAnnotation.read)
                                                                                                                        (PhraseType.fn  (PhraseType.expr dt2 DAnnotation.read)
                                                                                                                                        (PhraseType.expr dt3 DAnnotation.read))
                                                                                            | _ => throw s!"{primType} is no match for idx / add / sub / mult / div / gt / lt / equal / mod / gather" -- terminate

    | "scatter" => match primType with
                    | .fn (RType.data dt1) (RType.fn (RType.data dt2) (RType.data dt3)) =>
                          return PhraseType.fn (PhraseType.expr dt1 DAnnotation.read) (PhraseType.fn (PhraseType.expr dt2 DAnnotation.write) (PhraseType.expr dt3 DAnnotation.write))
                    | _ => throw s!"{primType} is no match for scatter" -- terminate

    | "natAsIndex" | "take" | "drop" => match primType with
                                        | .pi .nat _ userName (.fn (.data dt1) (.data dt2)) => return PhraseType.pi (.rise .nat) userName (.fn (.expr dt1 .read) (.expr dt2 .read))
                                        | _ => throw s!"{primType} is no match for natAsIndex" -- terminate

    | "reduceSeq" | "reduceSeqUnroll" => match primType with
                                          | .fn (RType.fn (RType.data t) (RType.fn (RType.data s) (RType.data _))) (RType.fn (RType.data _) (RType.fn (RType.data (RData.array n _)) (RType.data _))) =>
                                                  return PhraseType.fn
                                                          (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.expr t DAnnotation.write)))
                                                          (PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr t DAnnotation.read)))
                                          | _ => throw s!"{primType} is no match for reduceSeq / reduceSeqUnroll" -- terminate

    | "scanSeq" => match primType with
                    | .fn (RType.fn (RType.data s) (RType.fn (RType.data t) (RType.data _))) (RType.fn (RType.data _) (RType.fn (RType.data (RData.array n _)) (RType.data _))) =>
                          return PhraseType.fn
                                  (PhraseType.fn (PhraseType.expr s DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.expr t DAnnotation.write)))
                                  (PhraseType.fn (PhraseType.expr t DAnnotation.write) (PhraseType.fn (PhraseType.expr (RData.array n s) DAnnotation.read) (PhraseType.expr (RData.array n t) DAnnotation.write)))
                    | _ => throw s!"{primType} is no match for scanSeq"  -- terminate

    | "rotateValue" => match primType with
                        | .pi .nat _ sz (.fn (.fn (.data s) (.data _)) (.fn (.data (.array nIn dtIn)) (.data (.array nOut dtOut)))) => return PhraseType.pi (.rise .nat) sz (.fn (.fn (.expr s .read) (.expr s .write)) (.fn (.expr (.array nIn dtIn) .read) (.expr (.array nOut dtOut) .read)))
                        | _ => throw s!"{primType} is no match for rotateValue" -- terminate

    | "circularBuffer" =>  match primType with
                            | .pi .nat _ alloc
                                  (.pi .nat _ sz
                                        (.fn (.fn (.data s) (.data _))
                                             (.fn (.data (.array nIn dtIn))
                                                  (.data (.array nOut dtOut)))))
                                => return PhraseType.pi (.rise .nat) alloc
                                                        (.pi (.rise .nat) sz
                                                             (.fn (.fn (.expr s .read) (.expr s .write))
                                                                  (.fn (.expr (.array nIn dtIn) .read)
                                                                       (.expr (.array nOut dtOut) .read))))
                            | _ => throw s!"{primType} is no match for circularBuffer" -- terminate

    | "slide" | "padClamp" =>  match primType with
                                | .pi .nat _ sz
                                  (.pi .nat _ sp
                                        (.fn (.data dt1) (.data dt2)))
                                => return PhraseType.pi (.rise .nat) sz
                                                        (.pi (.rise .nat) sp
                                                             (.fn (.expr dt1 .read) (.expr dt2 .read)))
                                | _ => throw s!"{primType} is no match for slide / padClamp" -- terminate

    | "iterate" =>  match primType with
                      | .pi .nat _ k
                            (.fn (.pi .nat _ l
                                      (.fn (.data (.array n1 at1)) (.data (.array n2 at2))))
                                 (.fn (.data (.array n3 at3)) (.data (.array n4 at4))))
                         => return PhraseType.pi (.rise .nat) k
                                                 (.fn (.pi (.rise .nat) l
                                                           (.fn (.expr (.array n1 at1) .read) (.expr (.array n2 at2) .write)))
                                                      (.fn (.expr (.array n3 at3) .read) (.expr (.array n4 at4) .write)))
                      | _ => throw s!"{primType} is no match for iterate" -- terminate

    | "oclIterate" =>  match primType with
                        | .fn _ _ => return PhraseType.comm --TODO look at it again -> no address
                        | _ => throw s!"{primType} is no match for oclIterate" -- terminate

    | "select" => match primType with
                    | .fn (RType.data (RData.scalar RScalar.bool)) (RType.fn (RType.data t) (RType.fn (RType.data _) (RType.data _))) =>
                          return PhraseType.fn (PhraseType.expr (RData.scalar RScalar.bool) DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.fn (PhraseType.expr t DAnnotation.read) (PhraseType.expr t DAnnotation.read)))
                    | _ => throw s!"{primType} is no match for select"  -- terminate

    | "padEmpty" =>  match primType with
                      | .pi .nat _ r (.fn (.data (.array n t))
                                          (.data (.array _ _)))
                        => return PhraseType.pi (.rise .nat) r
                                                (.fn (.expr (.array n t) .write)
                                                     (.expr (.array (.plus n (.bvar 2 r)) t) .write)) ---> is that correct with the bvar?
                      | _ => throw s!"{primType} is no match for padEmpty" -- terminate

    | "padCst" =>  match primType with
                    | .pi .nat _ l
                          (.pi .nat _ q
                                (.fn (.data t)
                                     (.fn (.data (.array n _))
                                          (.data (.array _ _)))))
                      => return PhraseType.pi (.rise .nat) l
                                              (.pi (.rise .nat) q
                                                   (.fn (.expr t .read)
                                                        (.fn (.expr (.array n t) .read)
                                                             (.expr (.array (.plus (.bvar 3 l) (.plus (.bvar 2 q) n)) t) .read)))) -- is that correct with the b vars?
                    | _ => throw s!"{primType} is no match for padCast" -- terminate

    | "generate" => match primType with
                      | .fn (RType.fn (RType.data (RData.index n)) (RType.data t)) (RType.data (RData.array _ _)) =>
                            return PhraseType.fn (PhraseType.fn (PhraseType.expr (RData.index n) DAnnotation.read) (PhraseType.expr t DAnnotation.read)) (PhraseType.expr (RData.array n t) DAnnotation.read)
                      | _ => throw "generate"  -- terminate

    | _ => throw s!"no match for {prim}"  -- terminate


---------------- Infer functions ----------------------

mutual
partial def inferPhraseTypesMonadic (e : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (PhraseType × RExprNodePt × Subst) := do
  let (pt, rPt, s) ← inferPhraseTypesHelper e ctx isKernelParamFun
  if isKernelParamFun then
      match pt with
        | .expr dt  _ => match subUnifyPhraseType pt (PhraseType.expr dt DAnnotation.write) with
                          | some subst => return ((Subst.applyPt subst pt), rPt, (Subst.applySubst s subst))
                          | none => throw "The program does not specify how to write the result of the program into its output"
        | _ => return (pt, rPt, s)
  else return (pt, rPt, s)



partial def inferPhraseTypesHelper (e : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (PhraseType × RExprNodePt × Subst) := do
  let node := e.node
  match node with
    | .bvar idx name =>
        let val ← getFromCtx idx name ctx
        return (val, .bvar idx name ,{map := {} : Subst})
    | .const userName => inferPrimitive e.type userName
    | .lit v =>
        let lpt := PhraseType.expr (assertDataType e.type) DAnnotation.read
        return (lpt, .lit v,{map := {} : Subst})
    | .app fn arg => inferApp fn arg ctx (addsKernelParam e.type isKernelParamFun)
    | .depapp fn arg => inferDepApp fn arg ctx isKernelParamFun
    | .lam binderName binderType body => let inT := assertFunctionType e.type
                                         inferLambda binderName binderType body inT ctx isKernelParamFun  --- look at atgain
    | .deplam binderName binderKind body => inferDepLambda binderName binderKind body ctx isKernelParamFun



----- infer Primitive PhraseTypes -------------------

partial def inferPrimitive (primType : RType) (prim : Lean.Name) : InferM (PhraseType × RExprNodePt × Subst) := do
  let primitiveType ← matchPrimitiveType prim primType
  let _ := checkConsistency primType primitiveType
  return (primitiveType, .const prim,{map := {} : Subst})


--- infer application PhraseTypes -------------------

partial def inferApp (fn arg : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool ) : InferM (PhraseType × RExprNodePt × Subst) := do
  let (fType, fNode, fSubst) ← inferPhraseTypesMonadic fn ctx isKernelParamFun
  let (argType, argNode, argSubst) ← inferPhraseTypesMonadic arg ctx isKernelParamFun
  let argSubstFType := assertFunctionTypePt (Subst.applyPt argSubst fType)
  match argSubstFType with
    | .fn binderType body => let subst  ← match subUnifyPhraseType argType binderType with
                                | some y => pure  y
                                | none => throw s!"subUnifyPhraseType failed for {argType} and {binderType}"
                             let appType := Subst.applyPt subst body
                             let resSubst := Subst.applySubst subst (Subst.applySubst argSubst fSubst)
                             return (appType, mkApp fNode argNode argSubstFType binderType, resSubst)
    | _ => throw s!"{fn} is no function type"


--- infer dependent application PhraseTypes -------------------

partial def inferDepApp (fn : RExpr) (arg : RWrapper) (ctx : FunctionContext) (isKernelParamFun : Bool ) : InferM (PhraseType × RExprNodePt × Subst) := do
  let (fType, fNode, fSubst) ← inferPhraseTypesMonadic fn ctx isKernelParamFun
  let depAppType ← match (arg, fType) with
                          | (.nat n, .pi (.rise .nat) userName body) => pure (substituteNatInPhraseType n userName body)
                          | (.data dt, .pi (.rise .data) userName body)  => pure (substituteDataInPhraseType dt userName body)
                          | (_ , _) => throw s!"the argument does not match with the function type " --- access identifier is missing yet

  return (depAppType, mkDepApp fNode fType arg,fSubst)




--- infer Lambda PhraseTypes -------------------

partial def inferLambda (binderName : Lean.Name) (binderType : RType) (body : RExpr) (inT : RType) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (PhraseType × RExprNodePt × Subst) := do
  let xType ← if isKernelParamFun
                  then pure (PhraseType.expr (assertDataType inT) DAnnotation.read)
                  else type binderType
  let ctxWithX ← insertInCtx ctx binderName xType
  let (eType, eNode,eSubst) ← inferPhraseTypesMonadic body ctxWithX isKernelParamFun
  let lambdaType := PhraseType.fn (Subst.applyPt eSubst xType) eType

  -- set depth like before
  let cstate ← get
  set { cstate with depth := cstate.depth - 1}

  return (lambdaType, mkLam binderName binderType eNode eType, eSubst)



--- infer dependent Lambda Phrasetypes -------------------

partial def inferDepLambda (binderName : Lean.Name) (binderKind : RKind) (body : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : InferM (PhraseType × RExprNodePt × Subst) := do
  let (bodyType, bodyNode, bodySubst) ← inferPhraseTypesMonadic body ctx isKernelParamFun
  let depLamType := PhraseType.pi (DKind.rise binderKind) binderName bodyType
  return (depLamType, mkDepLam binderName binderKind bodyNode bodyType, bodySubst)

end

--- outer call
def inferPhraseTypes (e : RExpr) (ctx : FunctionContext) (isKernelParamFun : Bool) : (PhraseType × RExprNodePt × Subst) :=
  let result := (inferPhraseTypesMonadic e ctx isKernelParamFun).run {Counter := 0, ptAnnotationMap := {}}
  match result with
    | .ok ((pt, node,s), _) => (pt, node ,s)
    | .error msg => dbg_trace msg
                    (PhraseType.comm, .lit (.bool false) ,{map := {} : Subst}) --- want it to fail

def inferAccess (expr : RExpr) : RExprPt :=
  let (pt, node, subst) := inferPhraseTypes expr {} true
  {node := node, type := Subst.applyPt subst pt}
