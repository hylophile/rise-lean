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
        | .bvar idx name => let n ← getDepArgs name idx
                            return .bvar idx n
        | .nat _ => return nat
        | .plus n m =>  let x ← natRenaming n
                        let y ← natRenaming m
                        return .plus x y
        | .minus n m => let x ← natRenaming n
                        let y ← natRenaming m
                        return .minus x y
        | .mult n m => let x ← natRenaming n
                       let y ← natRenaming m
                       return .mult x y
        | .div n m => let x ← natRenaming n
                      let y ← natRenaming m
                      return .div x y
        | .pow n m => let x ← natRenaming n
                      let y ← natRenaming m
                      return .pow x y
        | _ => panic! s!"there should be no mvars naymore"

def dataRenaming (dt : RData): InferM RData := do
    match dt with
        | .bvar idx name => let n ← getDepArgs name idx
                            return .bvar idx n
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
        | .expr dt a => let d ← dataRenaming dt
                        return .expr d a
        | .comm => return .comm
        | .acc dt => let d ← dataRenaming dt
                     return .acc d
        | .pi n k body => let b ← typeRenaming body
                          return .pi n k b
        | .fn binderType body => let bt ← typeRenaming binderType
                                 let b ← typeRenaming body
                                 return .fn bt b
        | .phrasePair p1 p2 =>  let f ← typeRenaming p1
                                let s ← typeRenaming p2
                                return .phrasePair s f

def matchDepLam (p : DPIAPhrase): InferM Lean.Name := do
    match p.node with
        | .deplam name _ _ => updateDepArgs name
        | _ => pure (Lean.Name.mkSimple "dummy")

mutual
partial def uniqueRenaminfFunctional (In : FunctionalPrimitives): InferM FunctionalPrimitives := do
  match In with
    | .id val => let v ← uniqueRenamingHelper val
                 return .id v
    | .neg val => let v ← uniqueRenamingHelper val
                  return .neg v
    | .add lhs rhs => let x ← uniqueRenamingHelper lhs
                      let y ← uniqueRenamingHelper rhs
                      return .add x y
    | .sub lhs rhs => let x ← uniqueRenamingHelper lhs
                      let y ← uniqueRenamingHelper rhs
                      return .sub x y
    | .mul lhs rhs => let x ← uniqueRenamingHelper lhs
                      let y ← uniqueRenamingHelper rhs
                      return .mul x y
    | .div lhs rhs => let x ← uniqueRenamingHelper lhs
                      let y ← uniqueRenamingHelper rhs
                      return .div x y
    | .mod lhs rhs => let x ← uniqueRenamingHelper lhs
                      let y ← uniqueRenamingHelper rhs
                      return .mod x y
    | .not val => let v ← uniqueRenamingHelper val
                  return .not v
    | .gt lhs rhs => let x ← uniqueRenamingHelper lhs
                     let y ← uniqueRenamingHelper rhs
                     return .gt x y
    | .lt lhs rhs => let x ← uniqueRenamingHelper lhs
                     let y ← uniqueRenamingHelper rhs
                     return .lt x y
    | .equal lhs rhs => let x ← uniqueRenamingHelper lhs
                        let y ← uniqueRenamingHelper rhs
                        return .equal x y
    | .cast s t x => let sd ← dataRenaming s
                     let td ← dataRenaming t
                     let p ← uniqueRenamingHelper x
                     return .cast sd td p
    | .indexAsNat n idx => let num ← natRenaming n
                           let i ← uniqueRenamingHelper idx
                           return .indexAsNat num i
    | .natAsIndex n idx =>  let num ← natRenaming n
                            let i ← uniqueRenamingHelper idx
                            return .natAsIndex num i
    | .rlet s t a f val =>  let sd ← dataRenaming s
                            let td ← dataRenaming t
                            let fn ← uniqueRenamingHelper f
                            let v ← uniqueRenamingHelper val
                            return .rlet sd td a fn v
    | .toMem t input => let td ← dataRenaming t
                        let i ← uniqueRenamingHelper input
                        return .toMem td i
    | .generate n t f  => let num ← natRenaming n
                          let td ← dataRenaming t
                          let fn ← uniqueRenamingHelper f
                          return .generate num td fn
    | .idx n t idx array => let num ← natRenaming n
                            let td ← dataRenaming t
                            let i ← uniqueRenamingHelper idx
                            let a ← uniqueRenamingHelper array
                            return .idx num td i a
    | .depIdx ..  => return In -- needs to be fixed at some point
    | .idxVec n t idx vec  => let num ← natRenaming n
                              let td ← dataRenaming t
                              let i ← uniqueRenamingHelper idx
                              let v ← uniqueRenamingHelper vec
                              return .idxVec num td i v
    | .take n m t array => let num ← natRenaming n
                           let nm ← natRenaming m
                           let td ← dataRenaming t
                           let a ← uniqueRenamingHelper array
                           return .take num nm td a
    | .drop n m t array =>  let num ← natRenaming n
                            let nm ← natRenaming m
                            let td ← dataRenaming t
                            let a ← uniqueRenamingHelper array
                            return .drop num nm td a
    | .concat n m t nArray mArray => let num ← natRenaming n
                                     let nm ← natRenaming m
                                     let td ← dataRenaming t
                                     let nA ← uniqueRenamingHelper nArray
                                     let mA ← uniqueRenamingHelper mArray
                                     return .concat num nm td nA mA
    | .split n m t a array => let num ← natRenaming n
                              let nm ← natRenaming m
                              let td ← dataRenaming t
                              let arr ← uniqueRenamingHelper array
                              return .split num nm td a arr
    | .join n m t a array => let num ← natRenaming n
                             let nm ← natRenaming m
                             let td ← dataRenaming t
                             let arr ← uniqueRenamingHelper array
                             return .join num nm td a arr
    | .depJoin .. => return In  -- needs to be fixed at some point
    | .slide n sz sp t array => let num ← natRenaming n
                                let szn ← natRenaming sz
                                let spn ← natRenaming sp
                                let td ← dataRenaming t
                                let a ← uniqueRenamingHelper array
                                return .slide num szn spn td a
    | .circularBuffer n alloc sz s t load array => let num ← natRenaming n
                                                   let allocN ← natRenaming alloc
                                                   let szn ← natRenaming sz
                                                   let sd ← dataRenaming s
                                                   let td ← dataRenaming t
                                                   let loadP ← uniqueRenamingHelper load
                                                   let a ← uniqueRenamingHelper array
                                                   return .circularBuffer num allocN szn sd td loadP a
    | .rotateValues n sz t wrt array => let num ← natRenaming n
                                        let szn ← natRenaming sz
                                        let td ← dataRenaming t
                                        let a ← uniqueRenamingHelper array
                                        return .rotateValues num szn td wrt a
    | .transpose n m t a array => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let td ← dataRenaming t
                                  let arr ← uniqueRenamingHelper array
                                  return .transpose num nm td a arr
    | .cycle n m  t array  => let num ← natRenaming n
                              let nm ← natRenaming m
                              let td ← dataRenaming t
                              let arr ← uniqueRenamingHelper array
                              return .cycle num nm td arr
    | .reorder .. =>  return In  -- needs to be fixed at some point
    | .transposeDepArray .. =>  return In  -- needs to be fixed at some point
    | .gather n m t idx array => let num ← natRenaming n
                                 let nm ← natRenaming m
                                 let td ← dataRenaming t
                                 let i ← uniqueRenamingHelper idx
                                 let a ← uniqueRenamingHelper array
                                 return .gather num nm td i a
    | .scatter n m t idx array => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let td ← dataRenaming t
                                  let i ← uniqueRenamingHelper idx
                                  let a ← uniqueRenamingHelper array
                                  return .scatter num nm td i a
    | .padCst n l r t padExpr array =>  let num ← natRenaming n
                                        let rl ← natRenaming l
                                        let rn ← natRenaming r
                                        let td ← dataRenaming t
                                        let pE ← uniqueRenamingHelper padExpr
                                        let a ← uniqueRenamingHelper array
                                        return .padCst num rl rn td pE a
    | .padClamp n l r t array => let num ← natRenaming n
                                 let ln ← natRenaming l
                                 let rn ← natRenaming r
                                 let td ← dataRenaming t
                                 let a ← uniqueRenamingHelper array
                                 return .padClamp num ln rn td a
    | .padEmpty n r t array =>  let num ← natRenaming n
                                let rn ← natRenaming r
                                let td ← dataRenaming t
                                let a ← uniqueRenamingHelper array
                                return .padEmpty num rn td a
    | .zip n s t a sArray tArray => let num ← natRenaming n
                                    let sd ← dataRenaming s
                                    let td ← dataRenaming t
                                    let sA ← uniqueRenamingHelper sArray
                                    let tA ← uniqueRenamingHelper tArray
                                    return .zip num sd td a sA tA
    | .unzip n s t a array  =>  let num ← natRenaming n
                                let sd ← dataRenaming s
                                let td ← dataRenaming t
                                let arr ← uniqueRenamingHelper array
                                return .unzip num sd td a arr
    | .depZip ..  =>  return In  -- needs to be fixed at some point
    | .partition .. =>  return In  -- needs to be fixed at some point
    | .makePair s t a fst snd  => let sd ← dataRenaming s
                                  let td ← dataRenaming t
                                  let f ← uniqueRenamingHelper fst
                                  let sn ← uniqueRenamingHelper snd
                                  return .makePair sd td a f sn
    | .fst s t pair =>  let sd ← dataRenaming s
                        let td ← dataRenaming t
                        let p ← uniqueRenamingHelper pair
                        return .fst sd td p
    | .snd s t pair =>  let sd ← dataRenaming s
                        let td ← dataRenaming t
                        let p ← uniqueRenamingHelper pair
                        return .snd sd td p
    | .vectorFromScalar n t arg  => let num ← natRenaming n
                                    let td ← dataRenaming t
                                    let a ← uniqueRenamingHelper arg
                                    return .vectorFromScalar num td a
    | .asVector n m t a array  => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let td ← dataRenaming t
                                  let arr ← uniqueRenamingHelper array
                                  return .asVector num nm td a arr
    | .asVectorAligned n m t a array  => let num ← natRenaming n
                                         let nm ← natRenaming m
                                         let td ← dataRenaming t
                                         let arr ← uniqueRenamingHelper array
                                         return .asVectorAligned num nm td a arr
    | .asScalar n m t a array => let num ← natRenaming n
                                 let nm ← natRenaming m
                                 let td ← dataRenaming t
                                 let arr ← uniqueRenamingHelper array
                                 return .asScalar num nm td a arr
    | .map n s t a f array => let num ← natRenaming n
                              let sd ← dataRenaming s
                              let td ← dataRenaming t
                              let fn ← uniqueRenamingHelper f
                              let arr ← uniqueRenamingHelper array
                              return .map num sd td a fn arr
    | .mapSeq unroll n s t f array => let num ← natRenaming n
                                      let sd ← dataRenaming s
                                      let td ← dataRenaming t
                                      let fn ← uniqueRenamingHelper f
                                      let arr ← uniqueRenamingHelper array
                                      return .mapSeq unroll num sd td fn arr
    | .mapStream n s t f array  =>  let num ← natRenaming n
                                    let sd ← dataRenaming s
                                    let td ← dataRenaming t
                                    let fn ← uniqueRenamingHelper f
                                    let arr ← uniqueRenamingHelper array
                                    return .mapStream num sd td fn arr
    | .iterateStream n s t f array => let num ← natRenaming n
                                      let sd ← dataRenaming s
                                      let td ← dataRenaming t
                                      let fn ← uniqueRenamingHelper f
                                      let arr ← uniqueRenamingHelper array
                                      return .iterateStream num sd td fn arr
    | .depMapSeq .. => return In  -- needs to be fixed at some point
    | .mapVec n t1 t2 f vec  => let num ← natRenaming n
                                let t1d ← dataRenaming t1
                                let t2d ← dataRenaming t2
                                let fn ← uniqueRenamingHelper f
                                let v ← uniqueRenamingHelper vec
                                return .mapVec num t1d t2d fn v
    | .mapFst s1 t s2 a f pair => let s1d ← dataRenaming s1
                                  let td ← dataRenaming t
                                  let s2d ← dataRenaming s2
                                  let fn ← uniqueRenamingHelper f
                                  let p ← uniqueRenamingHelper pair
                                  return .mapFst s1d td s2d a fn p
    | .mapSnd s t1 t2 a f pair => let sd ← dataRenaming s
                                  let t1d ← dataRenaming t1
                                  let t2d ← dataRenaming t2
                                  let fn ← uniqueRenamingHelper f
                                  let p ← uniqueRenamingHelper pair
                                  return .mapSnd sd t1d t2d a fn p
    | .reduceSeq unroll n  s t f init array  => let num ← natRenaming n
                                                let sd ← dataRenaming s
                                                let td ← dataRenaming t
                                                let fn ← uniqueRenamingHelper f
                                                let i ← uniqueRenamingHelper init
                                                let arr ← uniqueRenamingHelper array
                                                return .reduceSeq unroll num sd td fn i arr
    | .scanSeq n s t f init array => let num ← natRenaming n
                                     let sd ← dataRenaming s
                                     let td ← dataRenaming t
                                     let fn ← uniqueRenamingHelper f
                                     let i ← uniqueRenamingHelper init
                                     let arr ← uniqueRenamingHelper array
                                     return .scanSeq num sd td fn i arr
    | .iterate n m k t f array => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let nk ← natRenaming k
                                  let td ← dataRenaming t
                                  let fn ← uniqueRenamingHelper f
                                  let arr ← uniqueRenamingHelper array
                                  return .iterate num nm nk td fn arr
    | .depTile n tileSize haloSize t1 t2 processTiles array  => let num ← natRenaming n
                                                                let tile ← natRenaming tileSize
                                                                let halo ← natRenaming haloSize
                                                                let t1d ← dataRenaming t1
                                                                let t2d ← dataRenaming t2
                                                                let process ← uniqueRenamingHelper processTiles
                                                                let arr ← uniqueRenamingHelper array
                                                                return .depTile num tile halo t1d t2d process arr
    | .printType msg t a input  =>  let td ← dataRenaming t
                                    let i ← uniqueRenamingHelper input
                                    return .printType msg td a i

partial def uniqueRenaminfImperative (In : ImperativePrimitives): InferM ImperativePrimitives := do
  match In with
    | .asScalarAcc n m t array => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let td ← dataRenaming t
                                  let arr ← uniqueRenamingHelper array
                                  return .asScalarAcc num nm td arr
    | .assign t lhs rhs =>  let td ← dataRenaming t
                            let l ← uniqueRenamingHelper lhs
                            let r ← uniqueRenamingHelper rhs
                            return .assign td l r
    | .asVectorAcc n m t array => let num ← natRenaming n
                                  let nm ← natRenaming m
                                  let td ← dataRenaming t
                                  let arr ← uniqueRenamingHelper array
                                  return .asVectorAcc num nm td arr
    | .forLoop unroll n body  => let num ← natRenaming n
                                 let b ← uniqueRenamingHelper body
                                 return .forLoop unroll num b
    | .forNat unroll n body =>  let num ← natRenaming n
                                let b ← uniqueRenamingHelper body
                                return .forNat unroll num b
    | .forVec n t out body => let num ← natRenaming n
                              let td ← dataRenaming t
                              let o ← uniqueRenamingHelper out
                              let b ← uniqueRenamingHelper body
                              return .forVec num td o b
    | .generateCont n t f  => let num ← natRenaming n
                              let td ← dataRenaming t
                              let fn ← uniqueRenamingHelper f
                              return .generateCont num td fn
    | .idxAcc n t idx array =>  let num ← natRenaming n
                                let td ← dataRenaming t
                                let i ← uniqueRenamingHelper idx
                                let arr ← uniqueRenamingHelper array
                                return .idxAcc num td i arr
    | .idxVecAcc n t idx vec => let num ← natRenaming n
                                let td ← dataRenaming t
                                let i ← uniqueRenamingHelper idx
                                let v ← uniqueRenamingHelper vec
                                return .idxVecAcc num td i v
    | .scatterAcc n m t indicies array => let num ← natRenaming n
                                          let nm ← natRenaming m
                                          let td ← dataRenaming t
                                          let i ← uniqueRenamingHelper indicies
                                          let arr ← uniqueRenamingHelper array
                                          return .scatterAcc num nm td i arr
    | .splitAcc n m t array => let num ← natRenaming n
                               let nm ← natRenaming m
                               let td ← dataRenaming t
                               let arr ← uniqueRenamingHelper array
                               return .splitAcc num nm td arr
    | .joinAcc n m t array => let num ← natRenaming n
                              let nm ← natRenaming m
                              let td ← dataRenaming t
                              let arr ← uniqueRenamingHelper array
                              return .joinAcc num nm td arr
    | .unzipAcc n t1 t2 array => let num ← natRenaming n
                                 let t1d ← dataRenaming t1
                                 let t2d ← dataRenaming t2
                                 let arr ← uniqueRenamingHelper array
                                 return .unzipAcc num t1d t2d arr
    | .zipAcc1     n t1 t2 array => let num ← natRenaming n
                                    let t1d ← dataRenaming t1
                                    let t2d ← dataRenaming t2
                                    let arr ← uniqueRenamingHelper array
                                    return .zipAcc1 num t1d t2d arr
    | .zipAcc2     n t1 t2 array => let num ← natRenaming n
                                    let t1d ← dataRenaming t1
                                    let t2d ← dataRenaming t2
                                    let arr ← uniqueRenamingHelper array
                                    return .zipAcc2 num t1d t2d arr
    | .transposeAcc n m t array  => let num ← natRenaming n
                                    let nm ← natRenaming m
                                    let td ← dataRenaming t
                                    let arr ← uniqueRenamingHelper array
                                    return .transposeAcc num nm td arr
    | .cycleAcc n m t input =>  let num ← natRenaming n
                                let nm ← natRenaming m
                                let td ← dataRenaming t
                                let i ← uniqueRenamingHelper input
                                return .cycleAcc num nm td i
    | .reorderAcc      .. => return In  -- needs to be fixed at some point
    | .dropAcc n m t array => let num ← natRenaming n
                              let nm ← natRenaming m
                              let td ← dataRenaming t
                              let arr ← uniqueRenamingHelper array
                              return .dropAcc num nm td arr
    | .takeAcc n m t array => let num ← natRenaming n
                              let nm ← natRenaming m
                              let td ← dataRenaming t
                              let arr ← uniqueRenamingHelper array
                              return .takeAcc num nm td arr
    | .mapAcc n t1 t2 f array => let num ← natRenaming n
                                 let t1d ← dataRenaming t1
                                 let t2d ← dataRenaming t2
                                 let fn ← uniqueRenamingHelper f
                                 let arr ← uniqueRenamingHelper array
                                 return .mapAcc num t1d t2d fn arr
    | .mapFstAcc t1 t2 t3 f record  =>  let t1d ← dataRenaming t1
                                        let t2d ← dataRenaming t2
                                        let t3d ← dataRenaming t3
                                        let fn ← uniqueRenamingHelper f
                                        let r ← uniqueRenamingHelper record
                                        return .mapFstAcc t1d t2d t3d fn r
    | .mapRead n t1 t2 f input =>   let num ← natRenaming n
                                    let t1d ← dataRenaming t1
                                    let t2d ← dataRenaming t2
                                    let fn ← uniqueRenamingHelper f
                                    let i ← uniqueRenamingHelper input
                                    return .mapRead num t1d t2d fn i
    | .mapSndAcc t1 t2 t3 f record => let t1d ← dataRenaming t1
                                      let t2d ← dataRenaming t2
                                      let t3d ← dataRenaming t3
                                      let fn ← uniqueRenamingHelper f
                                      let r ← uniqueRenamingHelper record
                                      return .mapSndAcc t1d t2d t3d fn r
    | .mkDPairFstl fst a => let f ← natRenaming fst
                            let ap ← uniqueRenamingHelper a
                            return .mkDPairFstl f ap
    | .mkDPairSndAcc fst sndT a => let f ← natRenaming fst
                                   let s ← dataRenaming sndT
                                   let ap ← uniqueRenamingHelper a
                                   return .mkDPairSndAcc f s ap
    | .pairAcc t1 t2 fst snd => let t1d ← dataRenaming t1
                                let t2d ← dataRenaming t2
                                let f ← uniqueRenamingHelper fst
                                let s ← uniqueRenamingHelper snd
                                return .pairAcc t1d t2d f s
    | .pairAcc1 t1 t2 pair => let t1d ← dataRenaming t1
                              let t2d ← dataRenaming t2
                              let p ← uniqueRenamingHelper pair
                              return .pairAcc1 t1d t2d p
    | .pairAcc2 t1 t2 pair =>   let t1d ← dataRenaming t1
                                let t2d ← dataRenaming t2
                                let p ← uniqueRenamingHelper pair
                                return .pairAcc2 t1d t2d p
    | .new t f => let td ← dataRenaming t
                  let fn ← uniqueRenamingHelper f
                  return .new td fn
    | .newDoubleBuffer n t1 t2 t3 input out f => let num ← natRenaming n
                                                 let t1d ← dataRenaming t1
                                                 let t2d ← dataRenaming t2
                                                 let t3d ← dataRenaming t3
                                                 let i ← uniqueRenamingHelper input
                                                 let o ← uniqueRenamingHelper out
                                                 let fn ← uniqueRenamingHelper f
                                                 return .newDoubleBuffer num t1d t2d t3d i o fn
    | .comment _ => return In
    | .skip => return In
    | .depIdxAcc .. => return In  -- needs to be fixed at some point
    | .depJoinAcc .. => return In  -- needs to be fixed at some point
    | .dMatchI x elemT outT f input =>  let xn ← natRenaming x
                                        let eT ← dataRenaming elemT
                                        let oT ← dataRenaming outT
                                        let fn ← uniqueRenamingHelper f
                                        let i ← uniqueRenamingHelper input
                                        return .dMatchI xn eT oT fn i
    | .seq c1 c2 => let p1 ← uniqueRenamingHelper c1
                    let p2 ← uniqueRenamingHelper c2
                    return .seq p1 p2

partial def uniqueRenamingHelper (p : DPIAPhrase) : InferM DPIAPhrase := do
    let idT ← matchDepLam p
    let type ← typeRenaming p.type
    let node ← match p.node with
                    | .bvar idx name => getArgs name idx
                    | .imperative imp => let i  ← uniqueRenaminfImperative imp
                                         pure (.imperative i)
                    | .functional prim => let f ← uniqueRenaminfFunctional prim
                                          pure (.functional f)
                    | .lit _ => pure p.node
                    | .app fn arg => let f ← uniqueRenamingHelper fn
                                     let a ← uniqueRenamingHelper arg
                                     pure (.app f a)
                    | .depapp fn arg => let f ← uniqueRenamingHelper fn
                                        pure (.depapp f arg)
                    | .lam name binderT body => let uBinder ← typeRenaming binderT
                                                let id ← updateArgs name
                                                let uBody ← uniqueRenamingHelper body
                                                updateDepth
                                                pure (.lam id uBinder uBody)
                    | .deplam _ binderK body => let uBody ← uniqueRenamingHelper body
                                                updateDepDepth
                                                pure (.deplam idT binderK uBody)
                    | .pair fst snd => let f ← uniqueRenamingHelper fst
                                       let s ← uniqueRenamingHelper snd
                                       pure (.pair f s)
                    | .proj1 p => let pr ← uniqueRenamingHelper p
                                  pure (.proj1 pr)
                    | .proj2 p => let pr ← uniqueRenamingHelper p
                                  pure (.proj1 pr)
                    | .ifThenElse cond thenP elseP => let c ← uniqueRenamingHelper cond
                                                      let t ← uniqueRenamingHelper thenP
                                                      let e ← uniqueRenamingHelper elseP
                                                      pure (.ifThenElse c t e)
    pure {node := node, type := type}

end

partial def uniqueRenaming (p : DPIAPhrase) : DPIAPhrase :=
    let result := (uniqueRenamingHelper p).run {}
    match result with
        | .ok (ph, _) => ph
        | .error msg => panic! s!"error ocurred during inferAccess: \n {msg}"
