import DPIA.mkFunctions
import DPIA.Substitutions

private abbrev IdentifierMap := Std.HashMap (Lean.Name × Nat) Lean.Name
private abbrev TypeMap := Std.HashMap (Lean.Name × Nat) Lean.Name

-- structure InferStateR where
--   counter : Nat := 0                                      -- counter for unique names
--   depth : Nat := 0
--   depDepth : Nat := 0
--   depArgs : TypeMap := {}
--   args : IdentifierMap := {}

-- private abbrev InferM := StateT InferStateR (Except String)

-- def lookUpId (name : Name) (idx : Nat) : InferM Name := do
--     let cstate : InferStateR ← get
--     match cstate.args.get? (name, (cstate.depth - idx)) with
--         | some y => pure y
--         | none => throw s!"unbound identifier {name}@{idx}"

-- def lookUpIdT (name : Name) (idx : Nat) : InferM Name := do
--     let cstate : InferStateR ← get
--     match cstate.depArgs.get? (name, (cstate.depDepth - idx)) with
--         | some y => pure y
--         | none => throw s!"unbound identifier {name}@{idx}"

-- def updateArgs (name : Name) : InferM Unit := do
--     let cstate : InferStateR ← get
--     let id := getFreshIdentifier "x" cstate.counter
--     let depth := cstate.depth
--     set {cstate with args := (cstate.args.insert (name, depth) id),
--                      counter := cstate.counter + 1,
--                      depth := cstate.depth + 1}

-- def updateDepArgs (name : Name) : InferM Unit := do
--     let cstate : InferStateR ← get
--     let id := getFreshIdentifier "x" cstate.counter
--     let depth := cstate.depDepth
--     set {cstate with depArgs := (cstate.depArgs.insert (name, depth) id),
--                      counter := cstate.counter + 1,
--                      depDepth := cstate.depDepth + 1}

-- def getArgs (name : Name) (idx : Nat) : InferM DPIAPhraseNode := do
--     let cstate ← get
--     match cstate.args.get? (name, (cstate.depth - idx)) with
--         | some y => pure (.bvar idx y)
--         | none => throw s!"unbound identifier {name}@{idx}"

-- def getDepArgs (name : Name) (idx : Nat) : InferM RData := do
--     let cstate ← get
--     match cstate.depArgs.get? (name, (cstate.depDepth - idx)) with
--         | some y => pure (.bvar idx y)
--         | none => throw s!"unbound identifier {name}@{idx}"

private def printMap : List ((Lean.Name × Nat) × Lean.Name) → String
    | [] => ""
    | ((name,idx), val) :: ys => s!"({name}×{idx}) → {val}\n" ++ printMap ys

def natRenaming (nat : RNat) (depArgs : TypeMap) (depth : Nat) : RNat :=
    match nat with
        | .bvar idx name =>  match depArgs.get? (name, (depth - idx-1)) with
                                | some y => .bvar idx y
                                | none => panic! s!"unbound identifier {nat} found during nat renaming"
        | .nat _ => nat
        | .plus n m => .plus (natRenaming n depArgs depth) (natRenaming m depArgs depth)
        | .minus n m => .plus (natRenaming n depArgs depth) (natRenaming m depArgs depth)
        | .mult n m => .plus (natRenaming n depArgs depth) (natRenaming m depArgs depth)
        | .div n m => .plus (natRenaming n depArgs depth) (natRenaming m depArgs depth)
        | .pow n m => .plus (natRenaming n depArgs depth) (natRenaming m depArgs depth)
        | _ => panic! s!"there should be no mvars naymore"

def dataRenaming (dt : RData) (depArgs : TypeMap) (depth : Nat): RData :=
    match dt with
        | .bvar idx name => match depArgs.get? (name, (depth - idx-1)) with
                                | some y => .bvar idx y
                                | none => panic! s!"unbound identifier {dt} found during data renaming"
        | .array n dt => .array n (dataRenaming dt depArgs depth)
        | .pair   dt1 dt2 => .pair (dataRenaming dt1 depArgs depth) (dataRenaming dt2 depArgs depth)
        | .index _ => dt
        | .scalar _ => dt
        | .natType => dt
        | .vector n dt => .vector n (dataRenaming dt depArgs depth)
        | _ => panic! s!"should not happen, mvars should be eliminated but got {dt}"

def typeRenaming (pt : PhraseType) (depArgs : TypeMap) (depth : Nat): PhraseType :=
    match pt with
        | .expr dt a => .expr (dataRenaming dt depArgs depth) a
        | .comm => .comm
        | .acc dt => .acc (dataRenaming dt depArgs depth)
        | .pi n k body => .pi n k (typeRenaming body depArgs depth)
        | .fn binderType body => .fn (typeRenaming binderType depArgs depth) (typeRenaming body depArgs depth)
        | .phrasePair p1 p2 => .phrasePair (typeRenaming p1 depArgs depth) (typeRenaming p2 depArgs depth)

def matchDepLam (p : DPIAPhrase) (depArgs : TypeMap) (depDepth : Nat) (counter : Nat): TypeMap × Nat :=
    match p.node with
        | .deplam name _ _ => ((depArgs.insert (name,depDepth) (getFreshIdentifier name.toString counter)), (depDepth+1))
        | _ => (depArgs, depDepth)

partial def uniqueRenamingHelper (p : DPIAPhrase) (args : IdentifierMap) (depArgs : TypeMap) (depth : Nat) (depDepth : Nat) (counter : Nat): DPIAPhrase :=
    let (depArgs', depDepth') := matchDepLam p depArgs depDepth counter
    let type := typeRenaming p.type depArgs' depDepth'
    let node := match p.node with
                    | .bvar idx name => match args.get? (name, (depth - idx-1)) with
                                            | some y => .bvar idx y
                                            | none => panic! s!"unbound identifier {p.node} found during renaming for key ({name},{depth - idx})"
                    | .imperative imp => .imperative (substituteInImperative imp (fun x => uniqueRenamingHelper x args depArgs depth depDepth counter) (fun x => dataRenaming x depArgs depDepth) (fun x => natRenaming x depArgs depDepth))
                    | .functional prim => .functional (substituteInFunctional prim (fun x => uniqueRenamingHelper x args depArgs depth depDepth counter) (fun x => dataRenaming x depArgs depDepth) (fun x => natRenaming x depArgs depDepth))
                    | .lit _ => p.node
                    | .app fn arg => .app (uniqueRenamingHelper fn args depArgs depth depDepth counter)
                                          (uniqueRenamingHelper arg args depArgs depth depDepth counter)
                    | .depapp fn arg => .depapp (uniqueRenamingHelper fn args depArgs depth depDepth counter)
                                                arg
                    | .lam name binderT body => let uBinder := typeRenaming binderT depArgs depDepth
                                                let id := getFreshIdentifier name.toString counter
                                                let uBody := uniqueRenamingHelper body (args.insert (name,depth) id) depArgs (depth+1) depDepth (counter +1)
                                                .lam id uBinder uBody
                    | .deplam name binderK body => let id := getFreshIdentifier name.toString counter
                                                   let uBody := uniqueRenamingHelper body args depArgs' depth (depDepth') (counter +1)
                                                   .deplam id binderK uBody
                    | .pair fst snd => .pair (uniqueRenamingHelper fst args depArgs depth depDepth counter)
                                             (uniqueRenamingHelper snd args depArgs depth depDepth counter)
                    | .proj1 p => .proj1 (uniqueRenamingHelper p args depArgs depth depDepth counter)
                    | .proj2 p => .proj2 (uniqueRenamingHelper p args depArgs depth depDepth counter)
                    | .ifThenElse cond thenP elseP => .ifThenElse (uniqueRenamingHelper cond args depArgs depth depDepth counter)
                                                                  (uniqueRenamingHelper thenP args depArgs depth depDepth counter)
                                                                  (uniqueRenamingHelper elseP args depArgs depth depDepth counter)
    {node := node, type := type}

partial def uniqueRenaming (p : DPIAPhrase) : DPIAPhrase :=
    uniqueRenamingHelper p {} {} 0 0 0
