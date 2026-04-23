import DPIA.mkFunctions
import DPIA.Substitutions

private abbrev IdentifierMap := Std.HashMap (Lean.Name × Nat) Lean.Name
private abbrev TypeMap := Std.HashMap (Lean.Name × Nat) Lean.Name

private def printMap : List ((Lean.Name × Nat) × Lean.Name) → String
    | [] => ""
    | ((name,idx), val) :: ys => s!"({name}×{idx}) → {val}\n" ++ printMap ys

structure InferStateR where
  counter : Nat := 0                                      -- counter for unique names
  depth : Nat := 0
  depDepth : Nat := 0
  depArgs : TypeMap := {}
  args : IdentifierMap := {}

private abbrev InferM := StateT InferStateR (Except String)

def lookUpId (name : Name) (idx : Nat) : InferM Name := do
    let cstate : InferStateR ← get
    match cstate.args.get? (name, (cstate.depth - idx)) with
        | some y => pure y
        | none => throw s!"unbound identifier {name}@{idx}"

def lookUpIdT (name : Name) (idx : Nat) : InferM Name := do
    let cstate : InferStateR ← get
    match cstate.depArgs.get? (name, (cstate.depDepth - idx)) with
        | some y => pure y
        | none => throw s!"unbound identifier {name}@{idx}"

def updateArgs (name : Name) : InferM Lean.Name := do
    let cstate : InferStateR ← get
    let id := getFreshIdentifier "x" cstate.counter
    let depth := cstate.depth
    set {cstate with args := (cstate.args.insert (name, depth) id),
                     counter := cstate.counter + 1,
                     depth := cstate.depth + 1}
    pure id

def updateDepArgs (name : Name) : InferM Lean.Name := do
    let cstate : InferStateR ← get
    let id := getFreshIdentifier "x" cstate.counter
    let depth := cstate.depDepth
    set {cstate with depArgs := (cstate.depArgs.insert (name, depth) id),
                     counter := cstate.counter + 1,
                     depDepth := cstate.depDepth + 1}
    pure id

def updateDepth : InferM Unit := do
    let cstate : InferStateR ← get
    set {cstate with depth := cstate.depth-1}

def updateDepDepth : InferM Unit := do
    let cstate : InferStateR ← get
    set {cstate with depDepth := cstate.depDepth-1}

def getArgs (name : Name) (idx : Nat) : InferM DPIAPhraseNode := do
    let cstate ← get
    match cstate.args.get? (name, (cstate.depth - idx -1)) with
        | some y => pure (.bvar idx y)
        | none => dbg_trace s!"{printMap cstate.args.toList}"
                  throw s!"unbound identifier {name}@{idx} at depth {cstate.depth}"

def getDepArgs (name : Name) (idx : Nat) : InferM Lean.Name := do
    let cstate ← get
    match cstate.depArgs.get? (name, (cstate.depDepth - idx - 1)) with
        | some y => pure y
        | none => throw s!"unbound identifier {name}@{idx}"

def natRenaming (nat : RNat) : InferM RNat := do
    match nat with
        | .bvar idx name => return .bvar idx (← getDepArgs name idx)
        | .nat _ => return nat
        | .plus n m =>  return .plus (← natRenaming n) (← natRenaming m)
        | .minus n m => return .minus (← natRenaming n) (← natRenaming m)
        | .mult n m => return .mult (← natRenaming n) (← natRenaming m)
        | .div n m => return .div (← natRenaming n) (← natRenaming m)
        | .pow n m => return .pow (← natRenaming n) (← natRenaming m)
        | _ => panic! s!"there should be no mvars naymore"

def dataRenaming (dt : RData): InferM RData := do
    match dt with
        | .bvar idx name => return .bvar idx (← getDepArgs name idx)
        | .array n dt => let num ← natRenaming n
                         let d ← dataRenaming dt
                         return .array num d
        | .pair   dt1 dt2 => let d1 ← dataRenaming dt1
                             let d2 ← dataRenaming dt2
                             return .pair d1 d2
        | .index _ => return dt
        | .scalar _ => return dt
        | .natType => return dt
        | .vector n dt => let num ← natRenaming n
                          let d ← dataRenaming dt
                          return .vector num d
        | _ => panic! s!"should not happen, mvars should be eliminated but got {dt}"

def typeRenaming (pt : PhraseType): InferM PhraseType := do
    match pt with
        | .expr dt a => return .expr (← dataRenaming dt) a
        | .comm => return .comm
        | .acc dt => return .acc (← dataRenaming dt)
        | .pi n k body => return .pi n k (← typeRenaming body)
        | .fn binderType body => return .fn (← typeRenaming binderType) (← typeRenaming body)
        | .phrasePair p1 p2 =>  return .phrasePair (← typeRenaming p1) (← typeRenaming p2)

def matchDepLam (p : DPIAPhrase): InferM Lean.Name := do
    match p.node with
        | .deplam name _ _ => updateDepArgs name
        | _ => pure (Lean.Name.mkSimple "dummy")

mutual
partial def uniqueRenaminfFunctional (In : FunctionalPrimitives): InferM FunctionalPrimitives := do
  match In with
    | .id val => return .id (← uniqueRenamingHelper val)
    | .neg val => return .neg (← uniqueRenamingHelper val)
    | .add lhs rhs => return .add (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .sub lhs rhs => return .sub (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .mul lhs rhs => return .mul (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .div lhs rhs => return .div (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .mod lhs rhs => return .mod (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .not val => return .not (← uniqueRenamingHelper val)
    | .gt lhs rhs => return .gt (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .lt lhs rhs => return .lt (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .equal lhs rhs => return .equal (← uniqueRenamingHelper lhs) (← uniqueRenamingHelper rhs)
    | .cast s t x => return .cast
                                (← dataRenaming s)  (← dataRenaming t)
                                (← uniqueRenamingHelper x)
    | .indexAsNat n idx => return .indexAsNat (← natRenaming n) (← uniqueRenamingHelper idx)
    | .natAsIndex n idx =>  return .natAsIndex (← natRenaming n) (← uniqueRenamingHelper idx)
    | .rlet s t a f val =>  return .rlet
                                        (← dataRenaming s) (← dataRenaming t) a
                                        (← uniqueRenamingHelper f) (← uniqueRenamingHelper val)
    | .toMem t input => return .toMem (← dataRenaming t) (← uniqueRenamingHelper input)
    | .generate n t f  => return .generate
                                    (← natRenaming n)
                                    (← dataRenaming t)
                                    (← uniqueRenamingHelper f)
    | .idx n t idx array => return .idx
                                    (← natRenaming n)
                                    (← dataRenaming t)
                                    (← uniqueRenamingHelper idx) (← uniqueRenamingHelper array)
    | .depIdx ..  => return In -- needs to be fixed at some point
    | .idxVec n t idx vec  => return .idxVec
                                        (← natRenaming n)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper idx) (← uniqueRenamingHelper vec)
    | .take n m t array => return .take
                                    (← natRenaming n) (← natRenaming m)
                                    (← dataRenaming t)
                                    (← uniqueRenamingHelper array)
    | .drop n m t array =>  return .drop
                                    (← natRenaming n) (← natRenaming m)
                                    (← dataRenaming t)
                                    (← uniqueRenamingHelper array)
    | .concat n m t nArray mArray => return .concat
                                                (← natRenaming n) (← natRenaming m)
                                                (← dataRenaming t)
                                                (← uniqueRenamingHelper nArray) (← uniqueRenamingHelper mArray)
    | .split n m t a array => return .split
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t) a
                                        (← uniqueRenamingHelper array)
    | .join n m t a array => return .join
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t) a
                                        (← uniqueRenamingHelper array)
    | .depJoin .. => return In  -- needs to be fixed at some point
    | .slide n sz sp t array => return .slide
                                            (← natRenaming n) (← natRenaming sz) (← natRenaming sp)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper array)
    | .circularBuffer n alloc sz s t load array => return .circularBuffer
                                                                (← natRenaming n) (← natRenaming alloc) (← natRenaming sz)
                                                                (← dataRenaming s) (← dataRenaming t)
                                                                (← uniqueRenamingHelper load) (← uniqueRenamingHelper array)
    | .rotateValues n sz t wrt array => return .rotateValues
                                                    (← natRenaming n) (← natRenaming sz)
                                                    (← dataRenaming t) wrt
                                                    (← uniqueRenamingHelper array)
    | .transpose n m t a array => return .transpose
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t) a
                                            (← uniqueRenamingHelper array)
    | .cycle n m  t array  => return .cycle
                                        (← natRenaming n)
                                        (← natRenaming m) (← dataRenaming t)
                                        (← uniqueRenamingHelper array)
    | .reorder .. =>  return In  -- needs to be fixed at some point
    | .transposeDepArray .. =>  return In  -- needs to be fixed at some point
    | .gather n m t idx array => return .gather
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper idx) (← uniqueRenamingHelper array)
    | .scatter n m t idx array => return .scatter
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper idx) (← uniqueRenamingHelper array)
    | .padCst n l r t padExpr array => return .padCst
                                                (← natRenaming n) (← natRenaming l) (← natRenaming r)
                                                (← dataRenaming t)
                                                (← uniqueRenamingHelper padExpr) (← uniqueRenamingHelper array)
    | .padClamp n l r t array => return .padClamp
                                            (← natRenaming n) (← natRenaming l) (← natRenaming r)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper array)
    | .padEmpty n r t array =>  return .padEmpty
                                            (← natRenaming n) (← natRenaming r)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper array)
    | .zip n s t a sArray tArray => return .zip
                                            (← natRenaming n)
                                            (← dataRenaming s) (← dataRenaming t) a
                                            (← uniqueRenamingHelper sArray)
                                            (← uniqueRenamingHelper tArray)
    | .unzip n s t a array  =>  return .unzip
                                        (← natRenaming n)
                                        (← dataRenaming s) (← dataRenaming t) a
                                        (← uniqueRenamingHelper array)
    | .depZip ..  =>  return In  -- needs to be fixed at some point
    | .partition .. =>  return In  -- needs to be fixed at some point
    | .makePair s t a fst snd  => return .makePair
                                            (← dataRenaming s) (← dataRenaming t) a
                                            (← uniqueRenamingHelper fst) (← uniqueRenamingHelper snd)
    | .fst s t pair =>  return .fst
                                (← dataRenaming s) (← dataRenaming t)
                                (← uniqueRenamingHelper pair)
    | .snd s t pair =>  return .snd
                                (← dataRenaming s) (← dataRenaming t)
                                (← uniqueRenamingHelper pair)
    | .vectorFromScalar n t arg  => return .vectorFromScalar
                                                (← natRenaming n)
                                                (← dataRenaming t)
                                                (← uniqueRenamingHelper arg)
    | .asVector n m t a array  => return .asVector
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t) a
                                            (← uniqueRenamingHelper array)
    | .asVectorAligned n m t a array  => return .asVectorAligned
                                                    (← natRenaming n) (← natRenaming m)
                                                    (← dataRenaming t) a
                                                    (← uniqueRenamingHelper array)
    | .asScalar n m t a array => return .asScalar
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t) a
                                            (← uniqueRenamingHelper array)
    | .map n s t a f array => return .map
                                        (← natRenaming n)
                                        (← dataRenaming s) (← dataRenaming t) a
                                        (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .mapSeq unroll n s t f array => return .mapSeq unroll
                                                (← natRenaming n)
                                                (← dataRenaming s) (← dataRenaming t)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .mapStream n s t f array  =>  return .mapStream
                                                (← natRenaming n)
                                                (← dataRenaming s) (← dataRenaming t)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .iterateStream n s t f array => return .iterateStream
                                                (← natRenaming n)
                                                (← dataRenaming s) (← dataRenaming t)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .depMapSeq .. => return In  -- needs to be fixed at some point
    | .mapVec n t1 t2 f vec  => return .mapVec
                                            (← natRenaming n)
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper vec)
    | .mapFst s1 t s2 a f pair => return .mapFst
                                            (← dataRenaming s1) (← dataRenaming t)
                                            (← dataRenaming s2) a
                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper pair)
    | .mapSnd s t1 t2 a f pair => return .mapSnd
                                            (← dataRenaming s) (← dataRenaming t1)
                                            (← dataRenaming t2) a
                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper pair)
    | .reduceSeq unroll n  s t f init array  => return .reduceSeq unroll
                                                            (← natRenaming n)
                                                            (← dataRenaming s) (← dataRenaming t)
                                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper init) (← uniqueRenamingHelper array)
    | .scanSeq n s t f init array => return .scanSeq
                                                (← natRenaming n)
                                                (← dataRenaming s) (← dataRenaming t)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper init) (← uniqueRenamingHelper array)
    | .iterate n m k t f array => return .iterate
                                            (← natRenaming n) (← natRenaming m) (← natRenaming k)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .depTile n tileSize haloSize t1 t2 processTiles array  => return .depTile
                                                                            (← natRenaming n) (← natRenaming tileSize) (← natRenaming haloSize)
                                                                            (← dataRenaming t1) (← dataRenaming t2)
                                                                            (← uniqueRenamingHelper processTiles) (← uniqueRenamingHelper array)
    | .printType msg t a input  => return .printType msg
                                                (← dataRenaming t) a
                                                (← uniqueRenamingHelper input)

partial def uniqueRenaminfImperative (In : ImperativePrimitives): InferM ImperativePrimitives := do
  match In with
    | .asScalarAcc n m t array => return .asScalarAcc
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper array)
    | .assign t lhs rhs =>  return .assign
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper lhs)
                                        (← uniqueRenamingHelper rhs)
    | .asVectorAcc n m t array => return .asVectorAcc
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper array)
    | .forLoop unroll n body  => return .forLoop unroll
                                            (← natRenaming n)
                                            (← uniqueRenamingHelper body)
    | .forNat unroll n body =>  return .forNat unroll
                                            (← natRenaming n)
                                            (← uniqueRenamingHelper body)
    | .forVec n t out body => return .forVec
                                        (← natRenaming n)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper out) (← uniqueRenamingHelper body)
    | .generateCont n t f  => return .generateCont
                                        (← natRenaming n)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper f)
    | .idxAcc n t idx array =>  return .idxAcc
                                        (← natRenaming n)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper idx) (← uniqueRenamingHelper array)
    | .idxVecAcc n t idx vec => return .idxVecAcc
                                        (← natRenaming n)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper idx) (← uniqueRenamingHelper vec)
    | .scatterAcc n m t indicies array => return .scatterAcc
                                                    (← natRenaming n) (← natRenaming m)
                                                    (← dataRenaming t)
                                                    (← uniqueRenamingHelper indicies) (← uniqueRenamingHelper array)
    | .splitAcc n m t array => return .splitAcc
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper array)
    | .joinAcc n m t array => return .joinAcc
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper array)
    | .unzipAcc n t1 t2 array => return .unzipAcc
                                            (← natRenaming n)
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper array)
    | .zipAcc1     n t1 t2 array => return .zipAcc1
                                            (← natRenaming n)
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper array)
    | .zipAcc2     n t1 t2 array => return .zipAcc2
                                            (← natRenaming n)
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper array)
    | .transposeAcc n m t array  => return .transposeAcc
                                                (← natRenaming n) (← natRenaming m)
                                                (← dataRenaming t)
                                                (← uniqueRenamingHelper array)
    | .cycleAcc n m t input =>  return .cycleAcc
                                            (← natRenaming n) (← natRenaming m)
                                            (← dataRenaming t)
                                            (← uniqueRenamingHelper input)
    | .reorderAcc      .. => return In  -- needs to be fixed at some point
    | .dropAcc n m t array => return .dropAcc
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper array)
    | .takeAcc n m t array => return .takeAcc
                                        (← natRenaming n) (← natRenaming m)
                                        (← dataRenaming t)
                                        (← uniqueRenamingHelper array)
    | .mapAcc n t1 t2 f array => return .mapAcc
                                            (← natRenaming n)
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper f) (← uniqueRenamingHelper array)
    | .mapFstAcc t1 t2 t3 f record  =>  return .mapFstAcc
                                                    (← dataRenaming t1) (← dataRenaming t2) (← dataRenaming t3)
                                                    (← uniqueRenamingHelper f) (← uniqueRenamingHelper record)
    | .mapRead n t1 t2 f input =>  return .mapRead
                                                (← natRenaming n)
                                                (← dataRenaming t1) (← dataRenaming t2)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper input)
    | .mapSndAcc t1 t2 t3 f record => return .mapSndAcc
                                                (← dataRenaming t1) (← dataRenaming t2) (← dataRenaming t3)
                                                (← uniqueRenamingHelper f) (← uniqueRenamingHelper record)
    | .mkDPairFstl fst a => return .mkDPairFstl
                                        (← natRenaming fst)
                                        (← uniqueRenamingHelper a)
    | .mkDPairSndAcc fst sndT a => return .mkDPairSndAcc
                                            (← natRenaming fst)
                                            (← dataRenaming sndT)
                                            (← uniqueRenamingHelper a)
    | .pairAcc t1 t2 fst snd => return .pairAcc
                                            (← dataRenaming t1) (← dataRenaming t2)
                                            (← uniqueRenamingHelper fst) (← uniqueRenamingHelper snd)
    | .pairAcc1 t1 t2 pair => return .pairAcc1
                                        (← dataRenaming t1) (← dataRenaming t2)
                                        (← uniqueRenamingHelper pair)
    | .pairAcc2 t1 t2 pair => return .pairAcc2
                                        (← dataRenaming t1) (← dataRenaming t2)
                                        (← uniqueRenamingHelper pair)
    | .new t f => return .new (← dataRenaming t) (← uniqueRenamingHelper f)
    | .newDoubleBuffer n t1 t2 t3 input out f => return .newDoubleBuffer
                                                            (← natRenaming n)
                                                            (← dataRenaming t1) (← dataRenaming t2) (← dataRenaming t3)
                                                            (← uniqueRenamingHelper input) (← uniqueRenamingHelper out) (← uniqueRenamingHelper f)
    | .comment _ => return In
    | .skip => return In
    | .depIdxAcc .. => return In  -- needs to be fixed at some point
    | .depJoinAcc .. => return In  -- needs to be fixed at some point
    | .dMatchI x elemT outT f input =>  return .dMatchI
                                                    (← natRenaming x)
                                                    (← dataRenaming elemT) (← dataRenaming outT)
                                                    (← uniqueRenamingHelper f) (← uniqueRenamingHelper input)
    | .seq c1 c2 => return .seq (← uniqueRenamingHelper c1) (← uniqueRenamingHelper c2)

partial def uniqueRenamingHelper (p : DPIAPhrase) : InferM DPIAPhrase := do
    let idT ← matchDepLam p
    let type ← typeRenaming p.type
    let node ← match p.node with
                    | .bvar idx name => getArgs name idx
                    | .imperative imp => pure (.imperative (← uniqueRenaminfImperative imp))
                    | .functional prim => pure (.functional (← uniqueRenaminfFunctional prim))
                    | .lit _ => pure p.node
                    | .app fn arg => pure (.app (← uniqueRenamingHelper fn)
                                                (← uniqueRenamingHelper arg))
                    | .depapp fn arg => pure (.depapp (← uniqueRenamingHelper fn) arg)
                    | .lam name binderT body => let uBinder ← typeRenaming binderT
                                                let id ← updateArgs name
                                                let uBody ← uniqueRenamingHelper body
                                                updateDepth
                                                pure (.lam id uBinder uBody)
                    | .deplam _ binderK body => let uBody ← uniqueRenamingHelper body
                                                updateDepDepth
                                                pure (.deplam idT binderK uBody)
                    | .pair fst snd => pure (.pair  (← uniqueRenamingHelper fst)
                                                    (← uniqueRenamingHelper snd))
                    | .proj1 p => pure (.proj1 (← uniqueRenamingHelper p))
                    | .proj2 p => pure (.proj1 (← uniqueRenamingHelper p))
                    | .ifThenElse cond thenP elseP => pure (.ifThenElse (← uniqueRenamingHelper cond)
                                                                        (← uniqueRenamingHelper thenP)
                                                                        (← uniqueRenamingHelper elseP))
                    | .natural _ => pure p.node
    pure {node := node, type := type}

end

partial def uniqueRenaming (p : DPIAPhrase) : DPIAPhrase :=
    let result := (uniqueRenamingHelper p).run {}
    match result with
        | .ok (ph, _) => ph
        | .error msg => panic! s!"error ocurred during Renaming: \n {msg}"
