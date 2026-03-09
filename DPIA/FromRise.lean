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


def primitives (name : Lean.Name) (type : PhraseType) : DPIAPhrase :=
  match name.toString with
    | "id" => panic! s!"not implemented yet"
    | "neg" => panic! s!"not implemented yet"

    | "add" => panic! s!"not implemented yet"
    | "sub" => panic! s!"not implemented yet"
    | "mul" => panic! s!"not implemented yet"
    | "div" => panic! s!"not implemented yet"
    | "mod" => panic! s!"not implemented yet"

    | "select" => panic! s!"not implemented yet"

    | "not" => panic! s!"not implemented yet"
    | "gt"  => panic! s!"not implemented yet"
    | "lt"  => panic! s!"not implemented yet"
    | "equal" => panic! s!"not implemented yet"

    | "cast" => panic! s!"not implemented yet"

    | "natAsNat" => panic! s!"not implemented yet"
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

    | "rlet" => panic! s!"not implemented yet"
    | "toMem" => panic! s!"not implemented yet"

    | "generate" => panic! s!"not implemented yet"
    | "idx" => panic! s!"not implemented yet"

    | "idxVex" => panic! s!"not implemented yet"

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

    | "makeArray" => panic! s!"not implemented yet"

    | "makePair" => panic! s!"not implemented yet"
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

    | "vectorFromScalar" => panic! s!"not implemented yet"
    | "asVector" => panic! s!"not implemented yet"
    | "asVectorAligned" => panic! s!"not implemented yet"
    | "asScalar" => panic! s!"not implemented yet"

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

    -- | "mapPar" => match type with
    --                 | PhraseType.fn (.fn (.expr s .read) (.expr t .write)) (.fn (.expr (.array n _) .read) (.expr (.array _ _) .write)) =>
    --                     let eType := (PhraseType.expr (.array n s) .read)
    --                     let eTypeOut := (PhraseType.expr (.array n t) .write)
    --                     let fType := (PhraseType.fn (.expr s .read) (.expr t .write))
    --                     let eFunType := (PhraseType.fn eType eTypeOut)
    --                     let type := PhraseType.fn fType eFunType

    --                     let map := mkMapPar n s t {node := .bvar 1 (Lean.Name.mkSimple "f") , type := fType : DPIAPhrase} {node := .bvar 0 (Lean.Name.mkSimple "array") , type := eType : DPIAPhrase}
    --                     let arrayNode := DPIAPhraseNode.lam (Lean.Name.mkSimple "array") eType map
    --                     let funNode := DPIAPhraseNode.lam (Lean.Name.mkSimple "f") fType {node := arrayNode, type := eFunType : DPIAPhrase}

    --                     {node := funNode, type := type : DPIAPhrase}
    --                 | _ => panic! s!"{type} is no valid map type"


    | "mapFst" => panic! s!"not implemented yet"
    | "mapSnd" => panic! s!"not implemented yet"

    | "reduce" => panic! s!"not implemented yet"
    | "reduceSeq" => match type with
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


    | "iterate" => panic! s!"not implemented yet"
    | "oclIterate" => panic! s!"not implemented yet"

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
