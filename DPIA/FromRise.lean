import DPIA.Basic
import Lean.Exception
import DPIA.Substitutions
import DPIA.Pimitives.Functional

--import DPIA.InferAccessAnnotation



--- expression --
private abbrev Context := Std.HashMap TypedRExpr PhraseType
private abbrev Name := Lean.Name.mkSimple

--mkMap (n : RNat) (s t : RData) (a : DAnnotation) (f array: DPIAPhrase)
def mkLam (type : PhraseType) (name : Lean.Name) (binderType : PhraseType) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .lam name binderType body, type := type : DPIAPhrase}

def mkDeplam (type : PhraseType) (name : Lean.Name) (binderKind : DKind) (body : DPIAPhrase) : DPIAPhrase :=
  {node := .deplam name binderKind body, type := type : DPIAPhrase}

def mkBvar (index : Nat) (name : Lean.Name) (type : PhraseType) : DPIAPhrase :=
  {node := .bvar index name, type := type : DPIAPhrase}

def buildArrayPrimitive (t: PhraseType) ()


def primitives (name : Lean.Name) (type : PhraseType) : DPIAPhrase :=
  match name.toString with
    | "id" => panic! s!"not implemented yet"

    | "neg" => match type with
                 | PhraseType.fn (.expr t .read) (.expr _ .read) =>

                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.expr t .read)) (Name "e") eType
                            (mkNeg t (mkBvar 0 (Name "e") eType))
                 | _ => panic! s!"{type} is no valid neg type"

    | "add" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr _ .read)) =>
                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkAdd t (mkBvar 1 (Name "e1") eType)
                                            (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid add type"

    | "sub" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr _ .read)) =>
                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkSub t (mkBvar 1 (Name "e1") eType)
                                            (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid sub type"

    | "mul" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr _ .read)) =>
                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkMul t (mkBvar 1 (Name "e1") eType)
                                            (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid mul type"

    | "div" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr _ .read)) =>
                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkDiv t (mkBvar 1 (Name "e1") eType)
                                            (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid div type"

    | "mod" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr _ .read)) =>
                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkMod t (mkBvar 1 (Name "e1") eType)
                                            (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid mod type"

    | "select" => match type with
                     | PhraseType.fn (.expr (.scalar .bool) .read)
                                     (.fn (.expr t .read)
                                          (.fn (.expr _ .read) (.expr _ .read))) =>
                            let fExprType := PhraseType.expr t .read
                            let tExprType := PhraseType.expr t .read
                            let condType := PhraseType.expr (.scalar .bool) .read
                            let fExprFunType := PhraseType.fn fExprType (.expr t .read)

                            mkLam (.fn condType (.fn tExprType fExprFunType)) (Name "cond") condType
                                   (mkLam (.fn tExprType fExprFunType) (Name "tExpr") tExprType
                                          (mkLam fExprFunType (Name "fExpr") fExprType
                                                 {node := (.ifThenElse (mkBvar 2 (Name "cond") condType) (mkBvar 1 (Name "tExpr") tExprType) (mkBvar 0 (Name "fExpr") fExprType)), type := .expr t .read : DPIAPhrase}))

                     | _ => panic! s!"{type} is no valid select type"

    | "not" => match type with
                  | PhraseType.fn (.expr (.scalar .bool) .read) (.expr (.scalar .bool) .read) =>

                            let eType := (.expr (.scalar .bool) .read)

                            mkLam (.fn eType (.expr (.scalar .bool) .read)) (Name "e") eType
                                   (mkNot (mkBvar 0 (Name "e ") eType))
                  | _ => panic! s!"{type} is no valid not type"

    | "gt"  => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr (.scalar .bool) .read)) =>

                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkGt  (mkBvar 1 (Name "e1") eType)
                                          (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid gt type"

    | "lt"  => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr (.scalar .bool) .read)) =>

                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkLt  (mkBvar 1 (Name "e1") eType)
                                          (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid lt type"

    | "equal" => match type with
                 | PhraseType.fn (.expr t .read)
                                 (.fn (.expr _ .read) (.expr (.scalar .bool) .read)) =>

                     let eType := PhraseType.expr t .read
                     mkLam (.fn eType (.fn eType eType)) (Name "e1") eType
                            (mkLam (.fn eType eType) (Name "e2") eType
                                   (mkGt (mkBvar 1 (Name "e1") eType)
                                         (mkBvar 0 (Name "e2") eType)))
                 | _ => panic! s!"{type} is no valid equal type"

    | "cast" => match type with
                  | PhraseType.fn  (.expr s .read)
                                   (.expr t .read) =>
                            let xType := PhraseType.expr s .read

                            mkLam  (.fn xType (.expr t .read)) (Name "x") xType
                                   (mkCast s t (mkBvar 0 (Name "x") xType))
                  | _ => panic! s!"{type} is no valid cast type"

    | "indexAsNat" => match type with
                        | PhraseType.fn   (.expr (.index n) .read)
                                          (.expr .natType .read) =>
                            let eType := PhraseType.expr (.index n) .read

                            mkLam   (.fn eType (.expr (.index n) .read)) (Name "e") eType
                                    (mkIndexAsNat n (mkBvar 0 (Name "e") eType))
                        | _ => panic! s!"{type} is no valid indexAsNat type"

    | "natAsIndex" => match type with
                      | PhraseType.pi (.rise .nat) name (.fn (.expr .natType .read) (.expr (.index n) .read)) =>
                          let eType := PhraseType.expr (.natType) .read
                          let eFunType := PhraseType.fn eType (.expr (.index n) .read)
                          let depType := PhraseType.pi (.rise .nat) name eFunType

                          mkDeplam depType name (.rise .nat)
                                   (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                          (mkNatAsIndex (.bvar 1 name)
                                                        {node:= (.bvar 0 (Name "e")), type := eType : DPIAPhrase}))

                      | _ => panic! s!"{type} is no valid natAsIndex type"

    | "rlet" => match type with
                  | PhraseType.fn  (.expr s .read)
                                   (.fn   (.fn (.expr _ .read) (.expr t a))
                                          (.expr _ _)) =>
                            let fType := PhraseType.fn (.expr s .read) (.expr t .read)
                            let xType := Phrasetype.expr (.expr s .read)
                            let fFunType := PhraseType.fn fType (.expr t a)

                            mkLam  (.fn xType fFunType) (Name "x") xType
                                   (mkLam fFunType (Name "f") fType
                                          (mkRLet s t a
                                                  (mkBvar 1 (Name "x") xType)
                                                  (mkBvar 0 (Name "f") fType)))
                  | _ => panic! s!"{type} is no valid let type"

    | "toMem" => match type with
                    | PhraseType.fn (.expr t .write) (.expr _ .read) =>

                        let eType := PhraseType.expr t .write

                        mkLam   (.fn eType (.expr t .read)) (Name "e") eType
                                (mkToMem t (mkBvar 0 (Name "e") eType))

                    | _ => panic! s!"not implemented yet"

    | "generate" => match type with
                     | PhraseType.fn (.fn (.expr (.index n) .read) (.expr t .read))
                                     (.expr (.array _ _) .read) =>
                            let fType := PhraseType.fn (.expr (.index n) .read) (.expr t .read)

                            mkLam  (.fn fType (.expr (.array n t) .read)) (Name "f") fType
                                   (mkGenerate n t (mkBvar 0 (Name "f") fType))
                     | _ => panic! s!"{type} is no valid generate type"

    | "idx" => match type with
                 | PhraseType.fn (.expr (.index n) .read)
                                 (.fn (.expr (.array _ t) .read)
                                      (.expr _ .read)) =>
                     let eType := PhraseType.expr (.array n t) .read
                     let iType := PhraseType.expr (.index n) .read
                     let eFunType := PhraseType.fn eType (.expr t .read)

                     mkLam (.fn iType eFunType) (Name "i") iType
                            (mkLam eFunType (Name "e") eType
                                   (mkIdx n t
                                          (mkBvar 1 (Name "i") iType)
                                          (mkBvar 0 (Name "e") eType)))
                 | _ => panic! s!"{type} is no valid index type"

    | "take" => match type with
                  | PhraseType.pi (.rise .nat) n
                                  (.fn (.expr (.array nm t) .read)
                                       (.expr (.array _ _) .read)) =>

                       let eType := PhraseType.expr (.array nm t) .read
                       let eFunType := PhraseType.fn eType (.expr (.array (.bvar 0 n) t) .read)

                       mkDeplam (.pi (.rise .nat) n eFunType) n (.rise .nat)
                                     (mkLam eFunType (Name "e") eType
                                            (mkTake (.bvar 1 n)
                                                    (.minus nm (.bvar 1 n) )
                                                    t
                                                    (mkBvar 1 (Name "e") eType)))

                  | _ => panic! s!"{type} is no valid take type"

    | "drop" => match type with
                  | PhraseType.pi (.rise .nat) n
                                  (.fn (.expr (.array nm t) .read)
                                       (.expr (.array _ _) .read)) =>
                       let eType := PhraseType.expr (.array nm t) .read
                       let eFunType := PhraseType.fn eType (.expr (.array (.minus nm (.bvar 0 n)) t) .read)

                       mkDeplam (.pi (.rise .nat) n eFunType) n (.rise .nat)
                                (mkLam eFunType (Name "e") eType
                                       (mkDrop (.bvar 1 n)
                                               (.minus nm (.bvar 0 n))
                                               t
                                               (mkBvar 1 (Name "e") eType)))

                  | _ => panic! s!"{type} is no valid drop type"

    | "concat" => panic! s!"not implemented yet"

    | "split" => match type with
                  | PhraseType.pi (.rise .nat) n (.fn (.expr (.array _ t) a) (.expr (.array m (.array _ _)) _)) =>
                      let eType := PhraseType.expr (.array (.mult m (.bvar 0 n)) t) a  -- should that be 0 or 1
                      let eFunType := PhraseType.fn eType (.expr (.array m (.array (.bvar 0 n) t)) a)
                      let depFunType := PhraseType.pi (.rise .nat) n (.fn eType (.expr (.array m (.array (.bvar 0 n) t)) a))

                      mkDeplam depFunType n (.rise .nat)
                               (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                      (mkSplit (.bvar 1 n) m t a
                                               {node := (.bvar 0 (Lean.Name.mkSimple "e")), type := eType : DPIAPhrase}))
                  | _ => panic! s!"{type} is no valid join type"

    | "join"  => match type with
                  | PhraseType.fn (.expr (.array n (.array m t)) a) (.expr (.array _ _) _) =>
                      let eType := PhraseType.expr (.array n (.array m t)) a
                      let eFunType := PhraseType.fn eType (.expr (.array (.mult n m) t) a)

                      mkLam eFunType (Lean.Name.mkSimple "e") eType
                            (mkJoin n m t a {node := (.bvar 0 (Lean.Name.mkSimple "e")), type := eType : DPIAPhrase})

                  | _ => panic! s!"{type} is no valid join type"


    | "slide" => match type with
                  | PhraseType.pi (.rise .nat) sz (.pi (.rise .nat) sp (.fn (.expr (.array insz t) .read) (.expr (.array np1 (.array _ _)) .read))) =>
                    let eType := PhraseType.expr (.array insz t) .read
                    let eFunType := PhraseType.fn eType (.expr (.array np1 (.array (.bvar 1 sz) t)) .read)
                    let innerDepType := PhraseType.pi (.rise .nat) sp (.fn eType (.expr (.array (.minus np1 (.nat 1)) (.array (.bvar 0 sz) t)) .read))

                    mkDeplam innerDepType sz (.rise .nat)
                             (mkDeplam innerDepType sp (.rise .nat)
                                       (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                              (mkSlide (.minus np1 (.nat 1))
                                                       (.bvar 2 sz)
                                                       (.bvar 1 sp)
                                                       t
                                                       {node := (.bvar 0 (Lean.Name.mkSimple "e")), type := eType : DPIAPhrase})))

                  | _ => panic! s!"{type} is no valid slide type"

    | "circularBuffer" => match type with
                            | PhraseType.pi (.rise .nat) alloc
                                            (.pi (.rise .nat) sz
                                                 (.fn (.fn (.expr s .read) (.expr t .write))
                                                      (.fn (.expr (.array insz _) .read) (.expr (.array n _) .read)))) =>

                                let eType := PhraseType.expr (.array insz s) .read
                                let eFunType := PhraseType.fn eType (.expr (.array n (.array (.bvar 1 sz) t)) .read)
                                let loadType := PhraseType.expr t .write
                                let loadFunType := PhraseType.fn loadType eFunType
                                let innerDepType := PhraseType.pi (.rise .nat) sz loadFunType

                                mkDeplam (.pi (.rise .nat) alloc innerDepType) alloc (.rise .nat)
                                         (mkDeplam innerDepType sz (.rise .nat)
                                                   (mkLam loadFunType (Name "load") loadType
                                                        (mkLam eFunType (Name "e") eType
                                                               (mkCircularBuffer n (.bvar 3 alloc) (.bvar 2 sz) s t
                                                                                    {node := (.bvar 1 (Name "load")), type := loadType}
                                                                                    {node := (.bvar 0 (Name "e")), type := eType}))))

                            | _ => panic! s!"{type} is no valid circularBuffer type"

    | "rotateValues" => match type with
                            | PhraseType.pi (.rise .nat) sz
                                            (.fn (.fn (.expr s .read) (.expr _ .write))
                                                 (.fn (.expr (.array insz _) .read)
                                                      (.expr (.array n _) .read))) =>

                               let eType := PhraseType.expr (.array insz s) .read
                               let eFunType := PhraseType.fn eType (.expr (.array n (.array (.bvar 1 sz) s)) .read)
                               let wrType := PhraseType.fn (.expr s .read) (.expr s .write)
                               let wrFunType := PhraseType.fn wrType eFunType

                               mkDeplam (.pi (.rise .nat) sz wrFunType) sz (.rise .nat)
                                        (mkLam wrFunType (Name "wr") wrType
                                               (mkLam eFunType (Name "e") eType
                                                      (mkRotatevalues n (.bvar 2 sz) s
                                                                      {node := (.bvar 1 (Name "wr")), type := wrType : DPIAPhrase}
                                                                      {node := (.bvar 0 (Name "e")), type := eType : DPIAPhrase} )))

                            | _ => panic! s!"{type} is no valid type for rotateValues"

    | "transpose" => match type with
                        | PhraseType.fn (.expr (.array n (.array m t)) a)
                                        (.expr (.array _ (.array _ _)) _) =>

                            let eType := PhraseType.expr (.array n (.array m t)) a
                            let eFunType := PhraseType.fn eType (.expr (.array m (.array n t)) a)

                            mkLam eFunType (Name "e") eType
                                  (mkTranspose n m t a
                                               {node := (.bvar 0 (Name "e")), type := eType : DPIAPhrase})
                        | _ => panic! s!"{type} is no valid type for transpose"

    | "gather" => match type with
                     | PhraseType.fn (.expr (.array m (.index n)) .read)
                                     (.fn (.expr (.array _ t) .read)
                                          (.expr (.array _ _) .read)) =>

                            let xType := PhraseType.expr (.array n t) .read
                            let xFunType := PhraseType.fn xType (.expr (.array m t) .read)
                            let yType := PhraseType.expr (.array m (.index n)) .read
                            let yFunType := PhraseType.fn yType xFunType

                            mkLam yFunType (Name "y") yType
                                  (mkLam xFunType (Name "x") xType
                                         (mkGather n m t
                                                   {node := (.bvar 1 (Name "y")), type := yType : DPIAPhrase}
                                                   {node := (.bvar 0 (Name "x")), type := xType : DPIAPhrase}))
                     | _ => panic! s!"{type} is no valid type for gather"

    | "scatter" => match type with
                     | PhraseType.fn (.expr (.array n (.index m)) .read)
                                     (.fn (.expr (.array _ t) .write)
                                          (.expr (.array _ _) .write)) =>

                            let xType := PhraseType.expr (.array n t) .write
                            let xFunType := PhraseType.fn xType (.expr (.array m t) .write)
                            let yType := PhraseType.expr (.array n (.index m)) .read
                            let yFunType := PhraseType.fn yType xFunType

                            mkLam yFunType (Name "y") yType
                                  (mkLam xFunType (Name "x") xType
                                         (mkScatter n m t
                                                   {node := (.bvar 1 (Name "y")), type := yType : DPIAPhrase}
                                                   {node := (.bvar 0 (Name "x")), type := xType : DPIAPhrase}))

                     | _ => panic! s!"{type} is no valid type for scatter"

    | "padCst" => match type with
                     | PhraseType.pi (.rise .nat) l
                                     (.pi (.rise .nat) q
                                          (.fn (.expr t .read)
                                               (.fn (.expr (.array n _) .read)
                                                    (.expr (.array _ _) .read)))) =>
                         let eType := PhraseType.expr (.array n t) .read
                         let eFunType := PhraseType.fn eType (.expr (.array (.plus (.bvar 2 l) (.plus n (.bvar 1 q))) t) .read)
                         let cstType := PhraseType.expr t .read
                         let cstFunType := PhraseType.fn cstType eFunType
                         let innerDepType := PhraseType.pi (.rise .nat) q cstFunType

                         mkDeplam (.pi (.rise .nat) l innerDepType) l (.rise .nat)
                                  (mkDeplam innerDepType q (.rise .nat)
                                            (mkLam cstFunType (Name "cst") cstType
                                                   (mkLam eFunType (Name "e") eType
                                                          (mkPadCst n (.bvar 3 l) (.bvar 2 q) t
                                                                   (mkBvar 1 (Name "cst") cstType)
                                                                   (mkBvar 0 (Name "e") eType)))))

                     | _ => panic! s!"{type} is no valid type for padCst"

    | "padClamp" => match type with
                       | PhraseType.pi (.rise .nat) l
                                       (.pi (.rise .nat) q
                                            (.fn (.expr (.array n t) .read)
                                                 (.expr (.array _ _) .read))) =>

                            let eType := PhraseType.expr (.array n t) .read
                            let eFunType := PhraseType.fn eType (.expr (.array (.plus (.bvar 1 l) (.plus (.bvar 0 q) n)) t) .read)
                            let innerDepType := PhraseType.pi (.rise .nat) q eFunType

                            mkDeplam (.pi (.rise .nat) l innerDepType) l (.rise .nat)
                                     (mkDeplam innerDepType q (.rise .nat)
                                               (mkLam eFunType (Name "e") eType
                                                      (mkPadClamp n (.bvar 2 l) (.bvar 1 q) t (mkBvar 0 (Name "e") eType))))
                       | _ => panic! s!"{type} is no valid type for padClamp"

    | "padEmpty" => match type with
                       | PhraseType.pi (.rise .nat) r
                                       (.fn (.expr (.array n t) .write)
                                            _) =>

                            let eType := PhraseType.expr (.array n t) .write
                            let eFunType := PhraseType.fn eType (.expr (.array (.plus n (.bvar 0 r)) t) .write)

                            mkDeplam (.pi (.rise .nat) r eFunType) r (.rise .nat)
                                     (mkLam eFunType (Name "e") eType
                                            (mkPadEmpty n (.bvar 1 r) t
                                                        (mkBvar 0 (Name "e") eType)))

                       | _ => panic! s!"{type} is no valid type for padEmpty"

    | "zip" => match type with
                 | PhraseType.fn (.expr (.array n s) a)
                                 (.fn (.expr (.array _ t) _)
                                      (.expr (.array _ (.pair _ _)) _) ) =>
                     let yType := PhraseType.expr (.array n t) a
                     let yFunType := PhraseType.fn yType (.expr (.array n (.pair s t)) a)
                     let xType := PhraseType.expr (.array n s) a

                     mkLam (.fn xType yFunType) (Name "y") yType
                           (mkLam yFunType (Name "y") yType
                                  (mkZip n s t a
                                         (mkBvar 1 (Name "x") xType)
                                         (mkBvar 0 (Name "y") yType)))

                 | _ => panic! s!"{type} is no valid type for zip"

    | "unzip" => match type with
                   | PhraseType.fn (.expr (.array n (.pair s t)) a)
                                   (.expr (.pair (.array _ _) (.array _ _)) _) =>
                       let eType := PhraseType.expr (.array n (.pair s t)) a
                       let eFunType := PhraseType.fn eType (.expr (.pair (.array n s) (.array n t)) a)

                       mkLam eFunType (Name "e") eType
                             (mkUnzip n s t a (mkBvar 0 (Name "e") eType))
                   | _ => panic! s!"{type} is no valid type for unzip"

    | "makePair" => match type with
                     | PhraseType.fn (.expr s a)
                                     (.fn (.expr t _)
                                          (.expr (.pair _ _) _)) =>
                            let yType := PhraseType.expr t a
                            let xType := PhraseType.expr s a
                            let yFunType := PhraseType.fn yType (.expr (.pair s t) a)
                            let xFunType := PhraseType.fn xType yFunType

                            mkLam xFunType (Name "x") xType
                                   (mkLam yFunType (Name "y") yType
                                          (mkMakePair s t a
                                                      (mkBvar 1 (Name "x") xType)
                                                      (mkBvar 0 (Name "y") yType)))

                     | _ => panic! s!"{type} is no valid type for makePair"

    | "fst" => match type with
                 | PhraseType.fn (.expr (.pair s t) .read)
                                 (.expr _ .read) =>
                     let eType := PhraseType.expr (.pair s t) .read

                     mkLam (.fn eType (.expr s .read)) (Name "e") eType
                           (mkFst s t (mkBvar 0 (Name "e") eType))
                 | _ => panic! s!"{type} is no valid type for fst"

    | "snd" => match type with
                 | PhraseType.fn (.expr (.pair s t) .read)
                                 (.expr _ .read) =>
                     let eType := PhraseType.expr (.pair s t) .read

                     mkLam (.fn eType (.expr t .read)) (Name "e") eType
                           (mkSnd s t (mkBvar 0 (Name "e") eType))
                 | _ => panic! s!"{type} is no valid type for snd"

    | "vectorFromScalar" => match type with
                              | PhraseType.fn    (.expr _ .read)
                                                 (.expr (.vector n t) .read) =>
                                   let eType := Phrasetype.expr t .read
                                   let eFunType := PhraseType.fn eType (.expr (.vector n t) .read)

                                   mkLam  eFunType (Name "e") eType
                                          (mkVectorFromScalar n t (mkBvar 0 (name "e") eType))
                              | _ => panic! s!"{type} is no valid vectorFromScalar type"

    | "asVector" => match type with
                     | PhraseType.pi (.rise .nat) n
                                     (.fn (.expr (.array mn _) a)
                                          (.expr (.array m (.vector _ t)) _)) =>

                            let eType := PhraseType.expr (.array mn t) a
                            let eFunType := PhraseType.fn eType (.expr (.array m (.vector (.bvar 0 n) t)) a)

                            mkDeplam      (.pi (.rise .nat) n eFunType) n (.rise .nat)
                                          (mkLam eFunType (Name "e") eType
                                                 (mkAsVector (.bvar 1 n) m t a (mkBvar 0 (Name "e") eType)))
                     | _ => panic! s!"{type} is no valid asVector type"

    | "asVectorAligned" => match type with
                     | PhraseType.pi (.rise .nat) n
                                     (.fn (.expr (.array mn _) a)
                                          (.expr (.array m (.vector _ t)) _)) =>
                            let eType := PhraseType.expr (.array mn t) a
                            let eFunType := PhraseType.fn eType (.expr (.array m (.vector (.bvar 0 n) t)) a)

                            mkDeplam      (.pi (.rise .nat) n eFunType) n (.rise .nat)
                                          (mkLam eFunType (Name "e") eType
                                                 (mkAsVectorAligned (.bvar 1 n) m t a (mkBvar 0 (Name "e") eType)))
                     | _ => panic! s!"{type} is no valid asVectorAligned type"

    | "asScalar" => match type with
                     | PhraseType.fn      (.expr (.array m (.vector n t)) a)
                                          (.expr (.array _ _) _) =>
                            let eType := PhraseType.expr (.array m (.vector n t)) a
                            let eFunType := PhraseType.fn eType (.expr (.array (.mult n m) t) a)

                            mkLam  eFunType (Name "e") eType
                                   (mkAsScalar n m t a (mkBvar 0 (Name "e") eType))

                     | _ => panic! s!"{type} is no valid asScalar type"

    | "map" => match type with
                | PhraseType.fn (.fn (.expr s ai) (.expr t _)) (.fn (.expr (.array n _) _) (.expr (.array _ _) _)) =>
                    let eType := (PhraseType.expr (.array n s) ai)
                    let fType := (PhraseType.fn (.expr s ai) (.expr t ai))
                    let eFunType := (PhraseType.fn eType (.expr (.array n t) ai))
                    let fFunType := PhraseType.fn fType eFunType

                    mkLam fFunType (Lean.Name.mkSimple "f") fType
                          (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                 (mkMap n s t ai
                                        {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                        {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase}))
                | _ => panic! s!"{type} is no valid map type"

    | "mapSeq" => match type with
                    | PhraseType.fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .write)) =>
                        let eType := (PhraseType.expr (.array n s) .read)
                        let fType := (PhraseType.fn (.expr s .read) (.expr t .write))
                        let eFunType := (PhraseType.fn eType (.expr (.array n t) .write))
                        let fFunType := PhraseType.fn fType eFunType

                        mkLam fFunType (Lean.Name.mkSimple "f") fType
                              (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                     (mkMapSeq false n s t
                                               {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                               {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase}))

                    | _ => panic! s!"{type} is no valid mapSeq type"

    | "mapSeqUnroll" => match type with
                          | PhraseType.fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .write)) =>
                              let eType := (PhraseType.expr (.array n s) .read)
                              let fType := (PhraseType.fn (.expr s .read) (.expr t .write))
                              let eFunType := (PhraseType.fn eType (.expr (.array n t) .write))
                              let fFunType := PhraseType.fn fType eFunType

                              mkLam fFunType (Lean.Name.mkSimple "f") fType
                                    (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                           (mkMapSeq true n s t
                                                     {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                     {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase}))

                          | _ => panic! s!"{type} is no valid mapSeqUnroll type"

    | "mapStream" => match type with
                      | PhraseType.fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .read)) =>
                          let eType := (PhraseType.expr (.array n s) .read)
                          let fType := (PhraseType.fn (.expr s .read) (.expr t .write))
                          let eFunType := (PhraseType.fn eType (.expr (.array n t) .read))
                          let fFunType := PhraseType.fn fType eFunType

                          mkLam fFunType (Lean.Name.mkSimple "f") fType
                                (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                       (mkMapStream n s t
                                                    {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                    {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase}))

                      | _ => panic! s!"{type} is no valid mapStream type"

    | "iterateStream" => match type with
                          | PhraseType.fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .write)) =>
                              let eType := (PhraseType.expr (.array n s) .read)
                              let fType := (PhraseType.fn (.expr s .read) (.expr t .write))
                              let eFunType := (PhraseType.fn eType (PhraseType.expr (.array n t) .write))
                              let fFunType := PhraseType.fn fType eFunType

                              mkLam fFunType (Lean.Name.mkSimple "f") fType
                                    (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                           (mkIterateStream n s t
                                                            {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                            {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase}))

                          | _ => panic! s!"{type} is no valid p type"

    | "mapFst" => match type with
                     | PhraseType.fn (.fn (.expr s a) (.expr s2 _))
                                     (.fn (.expr (.pair _ t) _) (.expr (.pair _ _) _)) =>
                            let fType := PhraseType.fn (.expr s a) (.expr s2 a)
                            let eType := PhraseType.expr (.pair s t) a
                            let eFunType := PhraseType.fn eType (.expr (.pair s2 t) a)
                            let fFunType := PhraseType.fn fType eFunType

                            mkLam fFunType (Name "f") fType
                                   (mkLam eFunType (Name "e") eType
                                          (mkMapFst s t s2 a
                                                    (mkBvar 1 (Name "f") fType)
                                                    (mkBvar 0 (Name "e") eType)))

                     | _ => panic! s!"{type} is no valid mapFst type"

    | "mapSnd" => match type with
                     | PhraseType.fn (.fn (.expr t a) (.expr t2 _))
                                     (.fn (.expr (.pair s _) _) (.expr (.pair _ _) _)) =>

                            let fType := PhraseType.fn (.expr t a) (.expr t2 a)
                            let eType := PhraseType.expr (.pair s t) a
                            let eFunType := PhraseType.fn eType (.expr (.pair s t2) a)
                            let fFunType := PhraseType.fn fType eFunType

                            mkLam fFunType (Name "f") fType
                                   (mkLam eFunType (Name "e") eType
                                          (mkMapFst s t t2 a
                                                    (mkBvar 1 (Name "f") fType)
                                                    (mkBvar 0 (Name "e") eType)))
                     | _ => panic! s!"{type} is no valid mapSnd type"

    | "reduce" => panic! s!"reduce has no implementation"

    | "reduceSeq" => match type with
                      | PhraseType.fn (.fn (.expr t .read) (.fn (.expr s .read) (.expr _ .write))) (.fn (.expr _ .write) (.fn (.expr (.array n _) .read) (.expr _ .read))) =>
                          let fType := PhraseType.fn (.expr t .read) (.fn (.expr s .read) (.expr t .write))
                          let iType := PhraseType.expr t .write
                          let eType := PhraseType.expr (.array n s) .read
                          let eFunType := PhraseType.fn eType (.expr t .read)
                          let iFunType := PhraseType.fn iType eFunType
                          let fFunType := PhraseType.fn fType iFunType

                          mkLam fFunType (Lean.Name.mkSimple "f") fType
                                (mkLam iFunType (Lean.Name.mkSimple "i") iType
                                       (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                             (mkReduceSeq false n s t
                                                          {node := .bvar 2 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                          {node := .bvar 1 (Lean.Name.mkSimple "i") , type := iType : DPIAPhrase}
                                                          {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase})))

                      | _ => panic! s!"{type} is no valid reduceSeq type"
    | "reduceSeqUnroll" =>  match type with
                              | PhraseType.fn (.fn (.expr t .read) (.fn (.expr s .read) (.expr _ .write))) (.fn (.expr _ .write) (.fn (.expr (.array n _) .read) (.expr _ .read))) =>
                                  let fType := PhraseType.fn (.expr t .read) (.fn (.expr s .read) (.expr t .write))
                                  let iType := PhraseType.expr t .write
                                  let eType := PhraseType.expr (.array n s) .read
                                  let fFunType := PhraseType.fn fType (.fn iType (.fn eType (.expr t .read)))
                                  let iFunType := PhraseType.fn iType (.fn eType (.expr t .read))
                                  let eFunType := PhraseType.fn eType (.expr t .read)

                                  mkLam fFunType (Lean.Name.mkSimple "f") fType
                                        (mkLam iFunType (Lean.Name.mkSimple "i") iType
                                               (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                                      (mkReduceSeq true n s t
                                                                   {node := .bvar 2 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                                   {node := .bvar 1 (Lean.Name.mkSimple "i") , type := iType : DPIAPhrase}
                                                                   {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase})))

                              | _ => panic! s!"{type} is no valid reduceSeq type"


    | "scanSeq" => match type with
                    | PhraseType.fn (.fn (.expr s .read) (.fn (.expr t .read) (.expr _ .write))) (.fn (.expr _ .write) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .write))) => --should the last one be .read or .write?

                        let fType := PhraseType.fn (.expr s .read) (.fn (.expr t .read) (.expr t .write))
                        let iType := PhraseType.expr t .write
                        let iFunType := PhraseType.fn iType (.expr (.array n t) .read)
                        let eType := PhraseType.expr (.array n s) .read
                        let eFunType := PhraseType.fn eType (.expr (.array n t) .write)
                        let fFunType := PhraseType.fn fType (.fn iType (.fn eType (.expr (.array n s) .write)))

                        mkLam fFunType (Lean.Name.mkSimple "f") fType
                              (mkLam iFunType (Lean.Name.mkSimple "i") iType
                                     (mkLam eFunType (Lean.Name.mkSimple "e") eType
                                            (mkScanSeq n s t {node := .bvar 2 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase}
                                                             {node := .bvar 1 (Lean.Name.mkSimple "i") , type := iType : DPIAPhrase}
                                                             {node := .bvar 0 (Lean.Name.mkSimple "e") , type := eType : DPIAPhrase})))
                    | _ => panic! s!"{type} is no valid scanSeq type" ---should i have the returntype as type?


    | "iterate" => match type with
                     | PhraseType.pi (.rise .nat) k
                                     (.fn (.pi   (.rise .nat) l
                                                 (.fn (.expr (.array ln t) .read)
                                                        (.expr (.array _ _) .write)))
                                          (.fn   (.expr (.array insz _) .read)
                                                 (.expr (.array m _) .write))) =>

                            let eType := PhraseType.expr (.array insz t) .read
                            let fType := PhraseType.pi (.rise .nat) l (.fn (.expr (.array ln t) .read) (.expr (.array (.bvar 0 l) t) .write))
                            let eFunType := PhraseType.fn eType (.expr (.array m t) .write)

                            mkDeplam      (.pi (.rise .nat) k (.fn fType eFunType)) k (.rise .nat)
                                          (mkLam (.fn fType eFunType) (Name "f") fType
                                                 (mkLam eFunType (Name "e") eType
                                                        (mkIterate    (.div ln (.bvar 0 l)) --> is that correct?
                                                                      m (.bvar 2 k) t
                                                                      (mkBvar 1 (Name "f") fType)
                                                                      (mkBvar 0 (Name "e") eType))))

                     | _ => panic! s!"{type} is no valid iterate type"

    | "oclIterate" => panic! s!"not implemented yet" --> do I need this one?

    | x => panic! s!"{x} is no valid primitive"
  --{node := (DPIAPhraseNode.bvar 0 name) , type := type : DPIAPhrase}

partial def expression (expr : TypedRExpr) (ptMap : Context) : DPIAPhrase :=
  let node := expr.node
  let val := ptMap.get? expr
  match val with
    | some type =>
        match node with
          | .bvar deBruijnIndex userName => let node := DPIAPhraseNode.bvar deBruijnIndex userName
                                            {node := node, type := type : DPIAPhrase}
          | .const userName =>  primitives userName type
          | .lit val => let node := DPIAPhraseNode.lit val
                        {node := node, type := type : DPIAPhrase}
          | .app fn arg =>  let eFn := expression fn ptMap -- do i need an instance of?
                            let eArg := expression arg ptMap
                            let node := DPIAPhraseNode.app eFn eArg
                            {node := node, type := type : DPIAPhrase}
          | .depapp fn arg => let eArg := DWrapper.rise arg
                              let eFn := expression fn ptMap -- do i need an instance of?
                              let node := DPIAPhraseNode.depapp eFn eArg
                              {node := node, type := type : DPIAPhrase}
          | .lam binderName binderType body =>  let ptBody := expression body ptMap
                                                let binderVal := ptMap.get? {node := (TypedRExprNode.bvar 0 binderName), type := binderType : TypedRExpr}
                                                match binderVal with
                                                  | some ptBinderType => let node := DPIAPhraseNode.lam binderName ptBinderType ptBody
                                                                         {node := node, type := type : DPIAPhrase}
                                                  | none => panic! s!"something went wrong, cannot find {binderName} in ptMap"
          | .deplam binderName binderKind body => let ptBinderKind := DKind.rise binderKind
                                                  let ptBody := expression body ptMap
                                                  let node := DPIAPhraseNode.deplam binderName ptBinderKind ptBody
                                                  {node := node, type := type :DPIAPhrase}
          | _ => panic! s!"Missing rule for mvar ond fvar"
    | none => panic! s!"something went wrong, cannot find {expr} in ptMap"
--termination_by TypedRExprSize expr

def fromRise (expr : TypedRExpr) : DPIAPhrase :=
  let rwMap := {} --inferAccess expr
  expression expr rwMap
