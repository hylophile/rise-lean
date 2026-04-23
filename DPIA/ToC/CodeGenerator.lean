import DPIA.ToC.env
import DPIA.mkFunctions
import DPIA.Substitutions
import DPIA.Pimitives.Functional
import DPIA.Pimitives.Imperative
import DPIA.betaReduction
import DPIA.ToC.Lifting

private abbrev mkName := Lean.Name.mkSimple
private abbrev Path := List PathExpr
private abbrev FstMember := PathExpr.pairAccess .fstMember
private abbrev SndMember := PathExpr.pairAccess .sndMember

------------------------ InferState for fresh names ---------------
private structure InferState where
  counter : Nat := 0                                      -- counter for unique names

private abbrev InferM := StateT InferState (Except String)

private def FreshIdentifier (name : String := "tmp") : InferM String := do
  let cstate : InferState ← get
  set { cstate with counter := cstate.counter + 1}
  return s!"{name}_{cstate.counter}"


------------------------ helper functions --------------------------
def mkNewName (name : Lean.Name) (s : String) : Lean.Name :=
    Lean.Name.mkSimple (name.toString ++ s)

def assertUnroll (unroll : Bool) : Bool :=
    if !unroll then true
    else panic! s!"there should not be any unrolls anymore"

def typeToStructNameComponent (t : RData) : String :=
    match t with
        | .index i => s!"idx {i}"
        | .array n dt => s!"{n}_{typeToStructNameComponent dt}"
        | .pair a b => s!"_{typeToStructNameComponent a}_{typeToStructNameComponent b}_"
        | .scalar _ | .natType | .vector _ _ => s!"{t}"
        | _ => panic! s!"cannot convert data type {t} to struct name component"

def typ (dt : RData) : CType :=
    match dt with
        | .scalar s => match s with
                        | .bool => .scalar (.int)
                        | .int => .scalar (.int)
                        | .i8 => .scalar (.i8)
                        | .i16 => .scalar (.i16)
                        | .i32 => .scalar (.i32)
                        | .i64 => .scalar (.i64)
                        | .u8 => .scalar (.u8)
                        | .u16 => .scalar (.u16)
                        | .u32 => .scalar (.u32)
                        | .u64 => .scalar (.u64)
                        | .f32 => .scalar (.float)
                        | .f64 => .scalar (.double)
                        | _ => panic! s!"{s} not supported"
        | .natType => .scalar (.int)
        | .index _ => .scalar (.int)
        | .array n dt => .array (typ dt) (some (RNatToCNatSimplified n))
        | .pair p1 p2 => .struct (mkName ("Record_" ++ typeToStructNameComponent p1 ++ "_" ++ typeToStructNameComponent p2))
                                 [{type := typ p1, userName := mkName "_fst"}, {type := typ p2, userName := mkName "_snd"}]
        | .bvar _ _ => panic! s!"did not expect {dt}"
        | _ => panic! s!"there should not be any mvars anymore"

def peelArrayLayers (dt : RData) : (Nat × RData) :=
    match dt with
        | .array _ et => let (n, d) := peelArrayLayers et
                         (n+1, d)
        | _ => (0, dt)

def splitAt (path : Path) (splitPoint : Nat) : (Path × Path) :=
    match splitPoint, path with
        | 0, _ => ([], path)
        | _, [] => panic! s!"empty list cannot be split at {splitPoint}"
        | _, x :: ys => let (p1, p2) := splitAt ys (splitPoint -1)
                        (x:: p1, p2)

def numberOfElementsUntil (arrayType : RData) (index : RNat) : RNat :=
    .mult (getTotalNumberOfElements arrayType)  index


partial def flattenIndicies (dt : RData) (indices : List RNat) : RNat :=
    match (dt, indices) with
        | (.array _ d, index :: rest) => .plus (numberOfElementsUntil d index)  (flattenIndicies d rest)
        | (_, []) => .nat 0
        | t => panic! s!"this pair combination should not happen {t}"


def flattenArrayIndicies (dt : RData) (path : Path) : (RData × RNat × Path) :=
    match dt with
        | .array _ _ => let (arrayLayers, dt2) := peelArrayLayers dt
                        let (indiciesAsPathElements, rest) := splitAt path arrayLayers
                        let indices := List.map (fun x => match x with
                                                            | .cIntExpr n => n
                                                            | _ => panic! s!"this should be a list of CIntExprs") indiciesAsPathElements
                        (dt2, flattenIndicies dt indices, rest)
        | _ => panic! s!"the data type should be an arraytype"

-- def genPad (n l r : Nat) (left right : CExpr) (i : PathExpr) (ps : Path) (array : DPIAPhrase) (env : Environment) (cont : CExpr → CStmt) : CStmt :=

def toNat (text : String) : RNat :=
    match text.toInt? with
        | some y => if y>= 0 then .nat y.toNat
                    else panic! s!"{y} is no nat"
        | none => panic! s!"{text} is not convertable to int"


---------------------- end of helper functions --------------------
partial def generateAccess (dt : RData) (expr : CExpr) (path: Path) (env : Environment) (cont : CExpr → InferM CStmt) : InferM CStmt :=
    match path with
        | [] => cont expr
        | PathExpr.pairAccess x :: ps => match dt with
                                | .pair p1 p2 => let (structMemeber, dt2) := match x with
                                                                                | .fstMember => ("_fst", p1)
                                                                                | .sndMember => ("_snd", p2)
                                                 generateAccess dt2 (.structMemberAccess expr (.declRef (mkName structMemeber))) ps env cont
                                | _ => panic! s!"expected tuple type"
        | PathExpr.cIntExpr _ :: _ => match dt with
                                        | .array _ _ => let (dt2, k, ps) := flattenArrayIndicies dt path
                                                        generateAccess dt2 (.arraySubscript expr (.arithmeticExpr (RNatToCNatSimplified k))) ps env cont
                                        | _ => panic! s!"Expected an array type that is accesed by the index but found {dt} instead."
        | _ => panic! s!"Cannot generate access for {dt} with this path {path}"

def codeGenLiteral (v : RLit) : CExpr :=
    match v with
        | .bool b => .literal s!"{b}"
        | .float f => .literal f
        | .int i => .literal s!"{i}"

def codeGenUnaryOp (op : CUnaryOp) (e : CExpr) : CExpr :=
    CExpr.unaryExpr op e

def codeGenBinaryOp (op : CBinaryOp) (e1 e2: CExpr) : CExpr :=
    .binaryExpr op e1 e2


mutual

partial def cmd (env : Environment) (p : DPIAPhrase) : InferM CStmt :=
    match p with
        | ⟨.ifThenElse cond thenP elseP, _ ⟩ => cond |> exp env [] (fun c => do return .ifThenElse c (← cmd env thenP) (some (← cmd env elseP)))
        | ⟨.bvar i n, .comm ⟩ => return lookUpCommEnv env n i
        | ⟨.app ⟨.bvar _ _, _⟩ _, _ ⟩ => return .breakStmt -- needs fixing here comes contEnv into play
        | ⟨.imperative imp, _⟩ => cmdImp env imp
        | ⟨.proj1 p, _⟩ => (liftPair p).1 |> cmd env
        | ⟨.proj2 p, _⟩ => (liftPair p).1 |> cmd env
        | ⟨.app fn arg, _⟩ => betaReduction fn arg |> cmd env
        | ⟨.depapp fn arg, _⟩ => dependentBetaReduction fn arg |> cmd env
        | _ => panic! s!"don't know how to generate code for {p.node}"

partial def cmdImp (env : Environment) (imp : ImperativePrimitives) : InferM CStmt := do
    match imp with
        | .skip => return .comment "skip"
        | .seq p1 p2=> return .stmts (← p1 |> cmd env) (← p2 |> cmd env)
        | .assign _ a e =>  e |> exp env [] (fun x => do
                                a |> acc env [] (fun y => do
                                    return .exprStmt (.assignment y x)))
        | .new dt ⟨.lam v t p, _⟩ => codeGenNew dt (mkBvar 0 v t) p env --- take a look at names again
--        | .newDoubleBuffer n _ _ dt inP outP ⟨.lam ps t p, _⟩ => codeGenNewDoubleBuffer (.array n dt) inP outP (mkBvar 0 ps t) p env  --- take a look at names again, not important for dot product
        | .forLoop u n b => match b.node with
                                | .lam i _ p => codeGenFor n i 0 p u env
                                | _ => panic! s!"the for-body should be a function"
        | .forNat u n b => match b.node with
                                | .deplam i (.rise .nat) p => codeGenFor n i 0 p u env
                                | _ => panic! s!"the for-body should be a function"
        | .comment msg => return .comment msg
--        | .dMatchI x inT _ f dPair => .breakStmt              -- not important for dot product
--        | .mkDPairFstl fst a => .breakStmt
        | _ => throw s!"don't know how to generate code for {imp}"

private partial def acc (env : Environment) (path : Path) (cont : CExpr → InferM CStmt) (p : DPIAPhrase) : InferM CStmt :=
    match p with
        | ⟨.bvar idx name, .acc dt⟩ =>  let expr := lookUpIdentEnv env name idx
                                        generateAccess dt expr path env cont
        | ⟨.imperative imp, _⟩ => imp |> accImp env path cont
        | ⟨.proj1 p, _⟩ => (liftPair p).1 |> acc env path cont
        | ⟨.proj2 p, _⟩ => (liftPair p).2 |> acc env path cont
        | _ => panic! s!"don't know how to generate code for {p.node}"

private partial def accImp (env : Environment) (path : Path) (cont : CExpr → InferM CStmt) (imp : ImperativePrimitives) : InferM CStmt := do
    match imp with
        -- | .splitAcc n _ _ a => match path with
        --                         | (.cIntExpr i) :: ps => a |> acc env ((.cIntExpr (.div i n)) :: (.cIntExpr (.mod i n)) :: ps) cont
        --                         | _ => panic! s!"expected a C-Integer-Expression on the path for splitAcc"
        | .joinAcc _ m _ a => match path with
                                | (.cIntExpr i) :: (.cIntExpr j) :: ps => a |> acc env ((.cIntExpr (.plus (.mult i m) j)) :: ps) cont
                                | _ => panic! s!"expected two C-Integer-Expression on the path for joinAcc"
        | .transposeAcc _ _ _ a => match path with
                                    | (.cIntExpr i) :: (.cIntExpr j) :: ps => a |> acc env ((.cIntExpr j) :: (.cIntExpr i) :: ps) cont
                                    | _ => panic! s!"expected two C-Integer-Expression on the path for joinAcc"
        | .pairAcc1 _ _ a => a |> acc env (FstMember :: path) cont
        | .pairAcc2 _ _ a => a |> acc env (SndMember :: path) cont
        | .pairAcc _ _ fst snd => match path with
                                    | (.pairAccess .fstMember) :: ps => fst |> acc env ps cont
                                    | (.pairAccess .sndMember) :: ps => snd |> acc env ps cont
                                    | [] => fst |> acc env [] (fun x => match x with
                                                                            | .structMemberAccess a1 _ => snd |> acc env [] (fun y => match y with
                                                                                                                                        | .structMemberAccess a2 _ => if a1 == a2 then cont a1
                                                                                                                                                                        else panic! s!"{a1} and {a2} should be the same"
                                                                                                                                        | _ => panic! s!"wrong CStmt")
                                                                            | _ => panic! s!"wrong CStmt")
                                    | _ => panic! s!"did not expect {path} for pairAcc"
        | .zipAcc1 _ _ _ a => match path with
                                | (.cIntExpr i) :: ps => a |> acc env ((.cIntExpr i) :: FstMember :: ps) cont
                                | _ => panic! s!"expected a C-Integer-Expression on the path for zipAcc1"
        | .zipAcc2 _ _ _ a => match path with
                                | (.cIntExpr i) :: ps => a |> acc env ((.cIntExpr i) :: SndMember :: ps) cont
                                | _ => panic! s!"expected a C-Integer-Expression on the path for zipAcc2"
        | .unzipAcc _ _ _ a => match path with
                                | (.cIntExpr i) :: (.pairAccess .fstMember) :: ps => a |> acc env (FstMember :: (.cIntExpr i) :: ps) cont
                                | (.cIntExpr i) :: (.pairAccess .sndMember) :: ps => a |> acc env (SndMember :: (.cIntExpr i) :: ps) cont
                                | _ => panic! s!"unexpected path {path}"
        | .takeAcc _ _ _ a => a |> acc env path cont
        | .dropAcc n _ _ a => match path with
                                | (.cIntExpr i) :: ps => a |> acc env ((.cIntExpr (.plus i n)) :: ps) cont
                                | _ => panic! s!"expected a C-Integer-Expression on the path for dropAcc"
        -- | .cycleAcc _ m _ a => match path with
        --                         | (.cIntExpr i) :: ps => a |> acc env ((.cIntExpr (.mod i n)) :: ps) cont
        | .scatterAcc n m _ y a =>  match path with
                                        | (.cIntExpr i) :: ps => let id := mkName (← FreshIdentifier "i")
                                                                 mkIdx n (.index m) (mkNatAsIndex n {node := .natural i, type := .expr .natType .read}) y |>
                                                                    exp env [] (fun yic => do
                                                                                            return .block [.declStmt (.var id (.scalar .int) (some yic)),
                                                                                                        (← a |> acc env ((.cIntExpr (.bvar 0 id)) :: ps) cont)])
                                        | _ => panic! s!"expected a C-Integer-Expression on the path for ScatterAcc"
        | .mapAcc n d _ f a => match path with
                                    | (.cIntExpr i) :: ps => betaReduction f (mkIdxAcc n d (mkNatAsIndex n {node := .natural i, type := .expr .natType .read}) a) |> acc env ps cont
                                    | _ =>  panic! s!"Expected a C-Integer-Expression on the path for mapAcc"
        | .mapFstAcc _ dt2 dt3 f a => match path with
                                        | (.pairAccess .fstMember) :: ps => betaReduction f (mkPairAcc1 dt3 dt2 a) |> acc env ps cont
                                        | (.pairAccess .sndMember) :: ps => mkPairAcc2 dt3 dt2 a |> acc env ps cont
                                        | _ => panic! s!"unexpected path {path} for mapFstAcc"
        | .mapSndAcc _ dt2 dt3 f a => match path with
                                        | (.pairAccess .fstMember) :: ps => mkPairAcc1 dt3 dt2 a |> acc env ps cont
                                        | (.pairAccess .sndMember) :: ps => betaReduction f (mkPairAcc2 dt3 dt2 a) |> acc env ps cont
                                        | _ => panic! s!"unexpected path {path} for mapFstAcc"
        | .idxAcc _ _ i a => codeGenIdxAcc i a env path cont
        | .mkDPairSndAcc _ _ a => a |> acc env ((.dPairSnd) :: path) cont
        | _ =>  panic! s!"don't know how to generate code for {imp}"


private partial def exp (env : Environment) (path : Path) (cont : CExpr → InferM CStmt) (p : DPIAPhrase) : InferM CStmt :=
    match p with
        | ⟨.bvar idx name, .expr dt _⟩ => let expr := lookUpIdentEnv env name idx
                                          generateAccess dt expr path env cont
        | ⟨.lit v, dt⟩ => match path with
                            | [] => match getDataType dt with
                                        | .index _ => cont (codeGenLiteral v)
                                        | .scalar _ => cont (codeGenLiteral v)
                                        | _ => panic! s!"expected an index type or scalar type but got {dt} for {p}"
                            | (.cIntExpr _) :: _ => panic! s!"this implementation has no array data yet!"
                            | _ => panic! s!"unexpected path {path}"
        | ⟨.natural n, _⟩ => match path with
                                | [] => cont (.arithmeticExpr  (RNatToCNatSimplified n))
                                | _ => throw s!"exprected the path to be empty"
        | ⟨.functional func, dt⟩ => func |> expFunc env path cont (getDataType dt)
        | ⟨.proj1 p, _⟩ => (liftPair p).1 |> exp env path cont -- left out simplifyNats as discussed
        | ⟨.proj2 p, _⟩ => (liftPair p).2 |> exp env path cont -- left out simplifyNats as discussed
        | _ => panic! s!"don't know how to generate code for {p.node}"

private partial def expFunc (env : Environment) (path : Path) (cont : CExpr → InferM CStmt) (dt : RData)  (func : FunctionalPrimitives) : InferM CStmt :=
    match func with
        | .neg v => match (dt, path) with
                        | (.scalar _, []) => v |> exp env [] (fun e => cont (codeGenUnaryOp .minus e))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .not v => match (dt,path) with
                        | (.scalar _, []) => v |> exp env [] (fun e => cont (codeGenUnaryOp .ex e))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .add n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.plus) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .sub n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.minus) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .div n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 => cont (codeGenBinaryOp (.div) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .mul n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.mult) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .mod n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.mod) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .gt n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.greaterThan) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .lt n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.lessThan) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .equal n m => match (dt, path) with
                        | (.scalar _, []) | (.natType, []) => n |> exp env [] (fun e1 =>
                                                                m |> exp env [] (fun e2 =>
                                                                    cont (codeGenBinaryOp (.equal) e1 e2)))
                        | _ => panic! s!"the path has to be empty and the data type has to be a scalar but got {path} and {dt} "
        | .cast _ dt e => match path with
                            | [] => e |> exp env [] (fun x => cont (.cast (typ dt) x))
                            | _ => panic! s!"expected the path to be empty for cast"
        | .indexAsNat _ e => e |> exp env path cont
        | .natAsIndex _ e => e |> exp env path cont
        | .split n _ _ _ e => match path with
                                | (.cIntExpr i) :: (.cIntExpr j) :: ps => e |> exp env ((.cIntExpr (.mult n (.mult i j)))::ps) cont
                                | _ => panic! s!"expected two C-Integer-Expressions on the path"
        | .join _ m _ _ e => match path with
                                | (.cIntExpr i) :: ps => e |> exp env ((.cIntExpr (.div m i)) :: (.cIntExpr (.div m i)) :: ps) cont
                                | _ => panic! s!"expected a C-Integer-Expressions on the path"
        -- | .partition _ _ _ _ e => match path with
        --                             | (.cIntExpr i) :: (.cIntExpr j) :: ps =>
        --                             | _ => panic! s!"expected two C-Integer-Expressions on the path for partitition".  ------ what is bigsum ?
        | .zip n dt1 dt2 _ e1 e2 => match path with
                                        | (.cIntExpr i) :: (.pairAccess xj) :: ps => match xj with
                                                                                        | .fstMember => e1 |> exp env ((.cIntExpr i) :: ps) cont
                                                                                        | .sndMember => e2 |> exp env ((.cIntExpr i) :: ps) cont
                                        | (.cIntExpr i) :: [] => let j := mkNatAsIndex n {node := .natural i, type := .expr .natType .read}
                                                                 let e := mkMakePair dt1 dt2 .read (mkIdx n dt1 j e1) (mkIdx n dt2 j e2)
                                                                 e |> exp env [] cont
                                        | _ => panic! s!"unexpected path {path} at zip"
        | .unzip _ _ _ _ e => match path with
                                | (.pairAccess xj) :: (.cIntExpr i) :: ps => e |> exp env ((.cIntExpr i) :: (.pairAccess xj) :: ps) cont
                                | _ => panic! s!"expected a tupel access followed by a C-Integer-Expression on the path but got {path}"
        | .makePair _ _ _ e1 e2 => match path with
                                    | (.pairAccess xj) :: ps => match xj with
                                                                    | .fstMember => e1 |> exp env ps cont
                                                                    | .sndMember => e2 |> exp env ps cont
                                    | [] => e1 |> exp env [] (fun ec1 =>
                                                e2 |> exp env [] (fun ec2 => cont (.recordLiteral (typ  dt) ec1 ec2)))
                                    | _ => panic! s!"unexpected path {path}"
        | .fst _ _ e => e |> exp env ((.pairAccess (.fstMember)) :: path) cont
        | .snd _ _ e => e |> exp env ((.pairAccess (.sndMember)) :: path) cont
        | .take _ _ _ e =>  e |> exp env path cont
        | .drop n _ _ e => match path with
                            | (.cIntExpr i) :: ps => e |> exp env ((.cIntExpr (.plus n i)) :: ps) cont
                            | _ => panic! s!"expected a C-Integer-Expression on the path for drop"
        -- | .cycle _ m _ e => match path with
        --                         | (.cIntExpr i) :: ps => e |> exp env ((.cIntExpr (.mod m i)) :: ps) cont
        --                         | _ => panic! s!"expected a C-Integer-Expression on the path for cycle"              --- no mod in RNat
        | .gather n m dt y e => match path with
                                    | (.cIntExpr i) :: ps => mkIdx n dt (mkIdx m (.index n) (mkNatAsIndex m {node := .natural i, type := .expr .natType .read}) y) e |> exp env ps cont
                                    | _ => panic! s!"unexpected path {path} for gather"
        -- | .padClamp n l r _ e => match path with
        --                             | (.cIntExpr i) :: ps => e |> exp env ((.cIntExpr 0) :: ps) (fun left =>
        --                                                         e |> exp env ((.cIntExpr (.minus n 1)) :: ps) (fun right =>
        --                                                             genPad))
        -- | .padCst n l r _ pad array
        | .slide _ _ s2 _ e => match path with
                                | (.cIntExpr i) :: (.cIntExpr j) :: ps => e |> exp env ((.cIntExpr (.plus (.mult i  s2) j)) :: ps) cont
                                | _ => panic! s!"expected two C-Integer-Expression on the path for slide"
        | .transpose _ _ _ _ e => match path with
                                    | (.cIntExpr i) :: (.cIntExpr j) :: ps => e |> exp env ((.cIntExpr j) :: (.cIntExpr i) :: ps) cont
                                    | _ => panic! s!"unexpected path {path} for transpose"
        | .map n dt _ _ f e => match path with
                                | (.cIntExpr i) :: ps => betaReduction f (mkIdx n dt (mkNatAsIndex n {node := .natural i, type := .expr .natType .read}) e) |> exp env ps cont
                                | _ => panic! s!"expected a C-Integer-Expression on the path for map"
        | .idx _ _ i e => codeGenIdx i e env path cont
        | _ =>  panic! s!"don't know how to generate code for {func}"




--------------------------- code Gen ----------------------------

partial def codeGenNew (dt : RData) (v p : DPIAPhrase) (env : Environment) : InferM CStmt :=
    match v with
        | ⟨.bvar i n, .phrasePair (.expr t1 rw) (.acc t2)⟩ => let ve := mkBvar i (mkNewName n "_e") (.expr t1 rw)
                                                             let va := mkBvar i (mkNewName n "_a") (.acc t2)
                                                             let vC := CExpr.declRef n
                                                             let env := updatedIdentEnv (updatedIdentEnv env (mkNewName n "_e") i vC) (mkNewName n "_a") i vC
                                                             let seq1 := CStmt.declStmt (.var n (typ dt) none)
                                                             let seq2 := substitutePhraseInPhrase {node := .pair ve va, type := .phrasePair (.expr t1 rw) (.acc t2)} p n
                                                             return .block [seq1, (← cmd env seq2)]
        | _ => panic! s!"type mismatch"

-- partial def codeGenNewDoubleBuffer (dt : RData) (inP outP ps p : DPIAPhrase) (env : Environment) : CStmt :=         --- not important for dot product
--     .breakStmt

partial def codeGenFor (n : RNat) (i : Lean.Name) (nt : Nat) (p : DPIAPhrase) (_ : Bool) (env : Environment) : InferM CStmt := do
    --  let _ := assertUnroll unroll
    --  let cI :=
    -- ignore applySubstitutions for now
    let name := mkName (<- FreshIdentifier "i_")
    let init := CDecl.var name (.scalar .int) (some (.arithmeticExpr (.nat 0)))
    let cond := CExpr.binaryExpr .less (.declRef name) (.arithmeticExpr (RNatToCNatSimplified n))
    let increment := CExpr.assignment (.declRef name) (.binaryExpr .plus (.declRef name) (.arithmeticExpr (.nat 1)))
    return .forLoop (.declStmt init) cond increment (.block [(<- p |> cmd (updatedIdentEnv env i nt (.declRef name)))])

--partial def codeGenForNat (n : RNat) (i : RNat) (p : DPIAPhrase) (unroll : Bool) (env : Environment) : InferM CStmt :=
--    return .breakStmt

partial def codeGenIdx (i e : DPIAPhrase) (env : Environment) (ps : Path) (cont : CExpr → InferM CStmt) : InferM CStmt :=
    i |> exp env [] (fun x => do  match x with
                                | .declRef n => e |> exp env ((.cIntExpr (.bvar 0 n)) :: ps) cont
                                | .arithmeticExpr ae => e |> exp env ((.cIntExpr (CNatToRNat ae)) :: ps) cont
                                | _ =>  let arithVar := mkName (← FreshIdentifier "idx")
                                        return CStmt.block [.declStmt (.var (mkName "idx") (.scalar .int) (some x)),
                                                     (← e |> exp env ((.cIntExpr (.bvar 0 arithVar)) :: ps) cont)])

partial def codeGenIdxAcc (i a : DPIAPhrase) (env : Environment) (ps : Path) (cont : CExpr → InferM CStmt) : InferM CStmt :=
    i |> exp env [] (fun x => do match x with
                                    | .literal text => a |> acc env ((.cIntExpr (toNat text)) :: ps) cont
                                    | .declRef name => a |> acc env ((.cIntExpr (.bvar 0 name)) :: ps) cont
                                    | .arithmeticExpr ae => a |> acc env ((.cIntExpr (CNatToRNat ae)) :: ps) cont
                                    | _ => let arithVar := mkName (← FreshIdentifier "idxAcc")
                                           return .block [.declStmt (.var arithVar (.scalar .int) (some x)),
                                                            (← a |> acc env ((.cIntExpr (.bvar 0 arithVar)) :: ps) cont)])

end

partial def generateWithFunctions (env : Environment) (p : DPIAPhrase) : CStmt :=
    let result := (cmd env p).run {}
    match result with
        | .ok (stmt, _) => stmt
        | .error msg => panic! s!"error ocurred during code generation: \n {msg}"
