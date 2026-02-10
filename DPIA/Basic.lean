import Rise.Basic

-- Kind
--   κ ::= nat | data |  (Natural Number Kind, Datatype Kind) | readWrite
-- all rise RKinds and readWrite
inductive DKind
  | rise (k: RKind)
  | readWrite
deriving BEq, Hashable, Repr


inductive DAnnotation
  | identifier (userName: Lean.Name) -- for now only a identifier -> gensym
  | read
  | write
deriving Repr, BEq

-- Types
--   τ ::= τ → τ | (x : κ) → τ (Data Type, Function Type, Dependent Function Type)
--         τ x τ | exp[dt , rw] | acc[ dt ] | Comm
inductive PhraseType
  | expr (dt : RData) (rw : DAnnotation)
  | comm
  | acc (dt : RData)
  | pi (binderKind : DKind) (userName : Lean.Name) (body : PhraseType)
  | fn (binderType : PhraseType) (body : PhraseType)
  | phrasePair (p1 : PhraseType) (p2 : PhraseType)
deriving Repr, BEq

-- all rise RWrappers plus readWrite
inductive DWrapper
  | rise (w: RWrapper)
  | readWrite (v: DAnnotation)
deriving Repr, BEq


mutual
structure DPIAPhrase where
  node: DPIAPhraseNode
  type: PhraseType
deriving Repr, BEq

inductive DPIAPhraseNode where
  | bvar (deBruijnIndex : Nat) (userName: Lean.Name)
  | imperative (imp : ImperativePrimitives)
  | functional (prim : FunctionalPrimitives)
  | lit (val : RLit)
  | app (fn arg : DPIAPhrase)
  | depapp (fn : DPIAPhrase) (arg : DWrapper)
  | lam (binderName : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase)
  | deplam (binderName : Lean.Name) (binderKind : DKind) (body : DPIAPhrase)
  | pair (fst snd: DPIAPhrase)
  | proj1 (p: DPIAPhrase)
  | proj2 (p: DPIAPhrase)
  | ifThenElse (cond thenP elseP: DPIAPhrase)
deriving Repr, BEq


--------- Functional primitives ---------------------

inductive FunctionalPrimitives where
  -- unary ops
  | id      (t : RData)
  | neg     (t : RData)

  -- binary ops
  | add     (lhs rhs : RData)
  | sub     (lhs rhs : RData)
  | mul     (lhs rhs : RData)
  | div     (lhs rhs : RData)
  | mod     (lhs rhs : RData)

  -- ternary ops
  | select  (t : RData) (cond : RData) -- TODO select : {t : data} → bool → t → t → t

  -- comparison ops
  | not     (v : RData) -- TODO not   :               bool → bool
  | gt      (lhs rhs : RData)
  | lt      (lhs rhs : RData)
  | equal   (lhs rhs : RData)

  -- cast ops
  | cast          (s t : RData)
  | indexAsNat    (n : RNat) (idx : DPIAPhrase)
  | natAsIndex    (n : RNat) (idx : DPIAPhrase)

  -- memory ops
  | rlet    (s t : RData) (a : DAnnotation) (f val: DPIAPhrase)
  | toMem   (t : RData) (input : DPIAPhrase)

  -- array ops
  | generate    (n : RNat) (t : RData) (f : DPIAPhrase)
  | idx         (n : RNat) (t : RData) (idx array : DPIAPhrase)

  | depIdx      (n ft idx: RNat) (array : DPIAPhrase)-- TODO (ft : NatToData)
  | idxVec      (n : RNat) (t : RData) (idx vec : DPIAPhrase)

  | take      (n m : RNat) (t : RData) (array : DPIAPhrase)
  | drop      (n m : RNat) (t : RData) (array : DPIAPhrase)
  | concat    (n m : RNat) (t : RData) (nArray mArray : DPIAPhrase)

  | split     (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | join      (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | depJoin   (n lenF : RNat) (t : RData) (array : DPIAPhrase) --TODO (lenF : NatToNat)

  | slide               (n sz sp : RNat) (t : RData) (array : DPIAPhrase)
  | circularBuffer      (n alloc sz : RNat) (s t : RData) (load array : DPIAPhrase)
  | rotateValues        (n sz : RNat) (t : RData) (wrt array : DPIAPhrase)

  | transpose           (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | cycle               (n m : RNat) (t : RData) (array : DPIAPhrase)
  | reorder             (n idxF : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase) -- TODO (idxF : NatToNat)
  | transposeDepArray   (n m ft : RNat) (array : DPIAPhrase) -- TODO (ft : NatToData)

  | gather      (n m : RNat) (t : RData) (idx array : DPIAPhrase)
  | scatter     (n m : RNat) (t : RData) (idx array : DPIAPhrase)

  | padCst      (n l r : RNat) (t : RData) (padExpr array : DPIAPhrase)
  | padClamp    (n l r : RNat) (t : RData) (array : DPIAPhrase)
  | padEmpty    (n r : RNat) (t : RData) (array : DPIAPhrase)

  | zip       (n : RNat) (s t : RData) (a : DAnnotation) (sArray tArray : DPIAPhrase)
  | unzip     (n : RNat) (s t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | depZip    (n ft1 ft2 : RNat) (e1 e2 : DPIAPhrase) -- TODO (ft1 ft2 : NatToData)

  | makeArray   (n : RNat) (t : RData) (elements : List DPIAPhrase) --- TODO (n : Int)

  | partition   (n m lenF : RNat) (t : RData) (array : DPIAPhrase) -- TODO (lenF : NatToNat)

  -- pair ops
  | makePair      (s t : RData) (a : DAnnotation) (fst snd : DPIAPhrase)
  | makeDepPair   (fst : RNat) (sndT : RData) (a : DAnnotation) (snd : DPIAPhrase)  -- TODO (fst : NatIdentifier)
  | fst           (s t : RData) (pair : DPIAPhrase)
  | snd           (s t : RData) (pair : DPIAPhrase)

  -- vector ops
  | vectorFromScalar    (n : RNat) (t : RData) (arg : DPIAPhrase)
  | asVector            (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | asVectorAligned     (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)
  | asScalar            (n m : RNat) (t : RData) (a : DAnnotation) (array : DPIAPhrase)

  -- map
  | map               (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase)
  | mapSeq            (unroll : Bool) (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | mapStream         (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | iterateStream     (n : RNat) (s t : RData) (f array: DPIAPhrase)
  | depMapSeq         (unroll : Bool) (n ft1 ft2 : RNat) (f array: DPIAPhrase) -- TODO (ft1 ft2 : NatToData)
  | mapVec            (n : RNat) (t1 t2 : RData) (f vec : DPIAPhrase)

  | mapFst    (s1 t s2 : RData) (a : DAnnotation) (f pair : DPIAPhrase)
  | mapSnd    (s t1 t2 : RData) (a : DAnnotation) (f pair : DPIAPhrase)

  -- reduce
  | reduceSeq (unroll : Bool) (n : RNat) (s t : RData) (f init array : DPIAPhrase )

  -- scan
  | scanSeq (n :RNat) (s t : RData) (f init array : DPIAPhrase)

  -- iterate
  | iterate (n m k : RNat) (t : RData) (f array : DPIAPhrase)

  -- ? TODO
  | depTile       (n tileSize haloSize : RNat) (t1 t2 : RData) (processTiles array : DPIAPhrase)
  | dMatch        (x : RNat) (elemT outT : RData) (a : DAnnotation) (f array : DPIAPhrase) -- TODO (x : NatIdentifier)
  | printType     (msg : String) (t : RData) (a : DAnnotation) (input : DPIAPhrase)
deriving Repr, BEq

------------- imperial primitives --------------------------

inductive ImperativePrimitives where

  -- vector ops
  | asScalarAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)
  | assign          (t : RData) (lhs rhs : DPIAPhrase)
  | asVectorAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  -- for ops
  | forLoop     (unroll : Bool) (n : RNat) (body : DPIAPhrase)-- for not possible as key -> unroll?
  | forNat      (unroll : Bool) (n : RNat) (body : DPIAPhrase)
  | forVec      (n : RNat) (t : RData) (out body : DPIAPhrase)

  -- array ops
  | generateCont    (n : RNat) (t : RData) (f : DPIAPhrase)
  | idxAcc          (n : RNat) (t : RData) (idx array: DPIAPhrase)
  | idxVecAcc       (n : RNat) (t : RData) (idx vec : DPIAPhrase)

  | scatterAcc      (n m : RNat) (t : RData) (indicies array : DPIAPhrase)

  | splitAcc    (n m : RNat) (t : RData) (array : DPIAPhrase)
  | joinAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  | unzipAcc    (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)
  | zipAcc1     (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)
  | zipAcc2     (n : RNat) (t1 t2 : RData) (array : DPIAPhrase)

  | transposeAcc    (n m : RNat) (t : RData) (array : DPIAPhrase)
  | cycleAcc        (n m : RNat) (t : RData) (input : DPIAPhrase)
  | reorderAcc      (n idxF : RNat) (t : RData) (array : DPIAPhrase) -- NatToNat? (idxF : natToNat)

  | dropAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)
  | takeAcc     (n m : RNat) (t : RData) (array : DPIAPhrase)

  -- map ops
  | mapAcc        (n : RNat) (t1 t2 t3 : RData) (f array : DPIAPhrase)
  | mapFstAcc     (t1 t2 t3 : RData) (f record : DPIAPhrase)
  | mapRead       (n : RNat) (t1 t2 t3 : RData) (f input : DPIAPhrase)
  | mapSndAcc     (t1 t2 t3 : RData) (f record : DPIAPhrase)

  -- pair ops
  | mkDPairFstl       (fst : RNat) (a : DPIAPhrase)
  | mkDPairSndAcc     (fst : RNat) (sndT : RData) (a : DPIAPhrase) --TODO: what does it do?

  | pairAcc     (t1 t2 : RData) (fst snd : DPIAPhrase)
  | pairAcc1    (t1 t2 : RData) (pair : DPIAPhrase)
  | pairAcc2    (t1 t2 : RData) (pair : DPIAPhrase)

  -- memory ops
  | new                 (t : RData) (f : DPIAPhrase)
  | newDoubleBuffer     (n : RNat) (t1 t2 t3 : RData) (input out f : DPIAPhrase)

  | comment   (comment : String)
  | skip

  -- ? TODO
  | depIdxAcc     (n idx ft: RNat) (array : DPIAPhrase) -- NatToNat? (ft : natToNat)
  | depJoinAcc    (n lenF : RNat) (t : RData) (array : DPIAPhrase)  -- NatToNat? (lenF : natToNat)
  | dMatchI       (x : RNat) (elemT outT : RData) (f input : DPIAPhrase) -- NatIdentifier? (x : natIdentifier)
  | seq           (c1 c2 : DPIAPhrase)

deriving Repr, BEq

end

------------ Representations ----------------------

-- modified from Nate
instance : ToString DKind where
  toString
    | DKind.rise k => s!"{k}"
    | DKind.readWrite => "rw"


instance : ToString DAnnotation where
  toString
    | .identifier name => s!"{name}"
    | .read => "rd"
    | .write => "wr"

-- modified from Nate
def PhraseType.toString : PhraseType → String
  | PhraseType.expr dt rw => s!"expr[{RData.toString dt} | {rw}]"
  | PhraseType.comm => s!"comm"
  | PhraseType.acc dt => s!" acc [{RData.toString dt}]"
  | PhraseType.pi kind un body =>
      s!"({un} : {kind}) → {PhraseType.toString body}"
  | PhraseType.fn binderType body =>
    match binderType with
    | .fn .. | .pi .. => s!"({PhraseType.toString binderType}) → {PhraseType.toString body}"
    | _ => s!"{PhraseType.toString binderType} → {PhraseType.toString body}"
  | PhraseType.phrasePair p1 p2 => s!"{PhraseType.toString p1} x {PhraseType.toString p2}"

-- modified from Nate
instance : ToString PhraseType where
  toString := PhraseType.toString

-- modified from Nate
def DWrapper.render : DWrapper -> Std.Format
  | .rise w => w.render
  | .readWrite v => toString v ++ " : readWrite"

-- modified from Nate
partial def DPIAPhraseNode.render : DPIAPhraseNode → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .imperative _ => s!"imperative is not defiend yet" --TODO | .imperative i
  | .functional _ => s!"functional is not defined yet" --TODO | .functional f
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | .app .. , _       => f.node.render ++ " " ++ e.node.render
    | _       , .app .. => f.node.render ++ " " ++ Std.Format.paren e.node.render
    | _       , _       => f.node.render ++ " " ++ e.node.render
  | .depapp f e   => f.node.render ++ " " ++ Std.Format.paren e.render
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} =>{Std.Format.line}{b.node.render}" ++ Std.Format.line
  | .pair fst snd => s!"({fst.node.render}, {snd.node.render})"
  | .proj1 _ => s!"proj1 not implemented yet" --TODO | .proj1 p
  | .proj2 _ => s!"proj2 not implemented yet" --TODO | .proj2 p
  | .ifThenElse cond thenP elseP => s!"if {cond.node.render}: \n {thenP.node.render}\n else: \n {elseP.node.render}" --TODO

-- modified from Nate
partial def DPIAPhraseNode.renderInline : DPIAPhraseNode → Std.Format
  | .bvar id n    => f!"{n}@{id}"
  | .imperative _ => s!"imperative is not defiend yet" --TODO | .imperative i
  | .functional _  => s!"functional is not defined yet" -- TODO | .functional f
  | .lit n        => s!"{n}"
  | .app f e      => match f.node, e.node with
    | .app .. , .app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | .app .. , _       => f.node.renderInline ++ " " ++ e.node.renderInline
    | _       , .app .. => f.node.renderInline ++ " " ++ Std.Format.paren e.node.renderInline
    | _       ,       _ => f.node.renderInline ++ " " ++ e.node.renderInline
  | .depapp f e   => f.node.renderInline ++ " " ++ Std.Format.paren e.render
  | .lam s t b    => Std.Format.paren s!"λ {s} : {t} => {b.node.renderInline}"
  | .deplam s k b => Std.Format.paren s!"Λ {s} : {k} => {b.node.renderInline}"
  | .pair fst snd => s!"({fst.node.renderInline}, {snd.node.renderInline})"
  | .proj1 _ => s!"proj1 not implemented yet" --TODO | .proj1 p
  | .proj2 _ => s!"proj2 not implemented yet" --TODO | .proj2 p
  | .ifThenElse cond thenP elseP => s!"if {cond.node.renderInline}: \n {thenP.node.renderInline}\n else: \n {elseP.node.renderInline}" --TODO

instance : Std.ToFormat DPIAPhraseNode where
  format := DPIAPhraseNode.render

instance : ToString DPIAPhraseNode where
  toString e := Std.Format.pretty e.render

-- copied from Nate
private def indent (s : String) : String :=
  s.trim |>.splitOn "\n" |>.map (λ s => "  " ++ s) |> String.intercalate "\n"

-- modified from Nate
instance : ToString DPIAPhrase where
  toString e := "expr:\n" ++ (indent <| toString e.node) ++ "\ntype:\n" ++ (indent <| toString e.type)
