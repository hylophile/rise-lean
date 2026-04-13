import DPIA.Basic
import DPIA.mkFunctions
import DPIA.betaReduction

private def mkNewName (name : Lean.Name) (s : String) : Lean.Name :=
    Lean.Name.mkSimple (name.toString ++ s)

partial def liftPair (p : DPIAPhrase) : (DPIAPhrase × DPIAPhrase) :=
    match p with
        | ⟨.bvar i n, .phrasePair dt1 dt2⟩ => (mkBvar i (mkNewName n "_1") dt1, mkBvar i (mkNewName n "_2") dt2)
        | ⟨.pair fst snd, _⟩ => (fst, snd)
        | ⟨.app fn arg, .phrasePair ..⟩ => let r := betaReduction fn arg
                                           liftPair r
        | ⟨.depapp fn arg, .phrasePair ..⟩ =>  let r := dependentBetaReduction fn arg
                                               liftPair r
        | ⟨.proj1 p, .phrasePair ..⟩ => let pair := liftPair p
                                        liftPair pair.1
        | ⟨.proj2 p, .phrasePair ..⟩ => let pair := liftPair p
                                        liftPair pair.2
        | _ => panic! s!"the given phrase is no valid pair"
