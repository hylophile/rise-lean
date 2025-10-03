import Rise.Basic
import Rise.SExprParser
import Regex

open IO

private unsafe def runZ3 (input : String) : Except Error (String × String) :=
  unsafeIO do
    let child ← do
      let (stdin, child) ← (← IO.Process.spawn {
        cmd := "z3",
        args := #["-in"],
        stdin := .piped,
        stdout := .piped,
        stderr := .piped
      }).takeStdin

      stdin.putStrLn input
      pure child
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    return (stdout, stderr)

unsafe def runSygus (input : String) : Except Error (String × String) :=
  -- dbg_trace input
  unsafeIO do
    let child ← do
      let (stdin, child) ← (← IO.Process.spawn {
        cmd := "cvc5",
        args := #["--lang", "sygus2"],
        -- args := #["--output-lang", "ast"]
        stdin := .piped,
        stdout := .piped,
        stderr := .piped
      }).takeStdin
      stdin.putStrLn input
      pure child
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    return (stdout, stderr)

private def s := "
(set-option :model.v2 true) (declare-const x_44 Int) (assert (= (+ 5 x_44) 7)) (check-sat) (get-model)
"

#eval runZ3 s

-- private def l : RNat := .plus (.nat 5) (.mvar 55 `x)
-- private def r : RNat := .nat 7

-- #eval "(-5)".toNat?

private def parseArrowFormat (input : String) : UnificationResult := do
  let lines := input.splitOn "\n"
  
  match lines.head? with
  | some "sat" => 
    let assignments := lines.tail?.getD []
    let mut result := []
    
    for line in assignments do
      let line := (line.splitOn "\"")[1]?.getD "" 
      let parts := line.splitOn "->"
      match parts.map (·.trim) with
      | name :: value ::[] => 
        match value.toNat? with
        | some n =>
          let id : Option RMVarId := (name.splitOn "_")[1]? >>= (·.toNat?)
          match id with
          | some id =>
              result := (id, .nat <| .nat n) :: result
          | none => .error <| .unsolved s!"parseArrowFormat: {input}"
        | none => .error <| .unsolved s!"parseArrowFormat: {input}"
      | _ => continue
    .ok result
  | _ => .error <| .unsolved s!"parseArrowFormat: {input}"

-- #eval parseArrowFormat "sat\nx_55 -> 5\ny_59 -> 8"


private def l1 : RNat := .plus (.nat 5) (.mvar 55 `x)
private def r1 : RNat := .bvar 23 `z

#eval runSygus (RNat.toSygus l1 r1)

-- private unsafe def s3 (smtlib : String) : UnificationResult :=
--   match runZ3 smtlib with
--   | .ok (s,_e) =>  
--     parseArrowFormat s
--   | _ => .none

private def z := "
  (
  (private define-fun p?3 ((q Real)) Real 5)
  (private define-fun r?5 ((q Real)) Real (- 5))
  )  
"

private def getMVarId (s : String) : Except String RMVarId :=
  match (s.splitOn "?")[1]? with
  | some s => match s.toNat? with
    | some n => .ok n
    | none => .error "mvar conv"
  | none => .error "mvar conv split"
  
private def Option.toUnificationResult : Option Substitution → String → UnificationResult
  | .some x, _ => .ok x
  | .none, _ => .error <| .unsolved s

private def parseSygus (s: String) : UnificationResult :=
  let re := re! r"-fun (\w+[\.\?]\d+) .* Real (.*)\)\n"
  let matchs := re.captureAll s
  let names := matchs.filterMap (fun x => (x.get 1) >>= (some ·.toString)) |>.map getMVarId
  let exprs := matchs.filterMap (fun x => (x.get 2) >>= (some ·.toString)) |>.map parseRNatSExpr
  
  if names.size != exprs.size then
    .error <| .unsolved "parseSygus"
  else
    names.zipWith f exprs |>.toList |>.mapM id |>.toUnificationResult "parseSygus"
    where
      f : Except String RMVarId → Except String RNat → Option (RMVarId × SubstEnum)
      | .ok id, .ok e => some (id, .nat e)
      | _, _ => none
        
#eval parseSygus z



-- #eval solveWithZ3 l r
-- #eval s3 s



private unsafe def solveWithZ3 (l r : RNat) : UnificationResult :=
  let smtlib := RNat.toSMTLib l r
  match runZ3 smtlib with
  | .ok (s,_e) =>  
    match parseArrowFormat s with
    | .ok x => .ok x
    | e => let x : UnificationResult := .error <| .unsolved smtlib
        x.merge e
  | _ => .error <| .unsolved "z3"

private unsafe def solveWithSygus (l r : RNat) : UnificationResult :=
  let s := RNat.toSygus l r
  match runSygus s with
  | .ok (s,_) =>
    parseSygus s
  | _ => .error <| .unsolved "sygus"

unsafe def solve (l r : RNat) : UnificationResult :=
  if l.hasBVar || r.hasBVar then
    solveWithSygus l r
  else
    solveWithZ3 l r

