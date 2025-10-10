import Rise.Basic
import Rise.SExprParser
import Regex

open IO


namespace RNat


-- TODO: the .get! calls are sad.
-- 
def toSMTTerm : RNat → Option String
  | .bvar ..       => none
  | .mvar id name  => some s!"{name}_{id}"
  | .nat n         => some s!"{n}"
  | .plus n m      => some s!"(+ {n.toSMTTerm.get!} {m.toSMTTerm.get!})"
  | .minus n m     => some s!"(- {n.toSMTTerm.get!} {m.toSMTTerm.get!})"
  | .mult n m      => some s!"(* {n.toSMTTerm.get!} {m.toSMTTerm.get!})"
  | .div n m      => some s!"(/ {n.toSMTTerm.get!} {m.toSMTTerm.get!})"
  | .pow n m       => some s!"(^ {n.toSMTTerm.get!} {m.toSMTTerm.get!})"

def toSygusTerm (n:RNat) (bvname:String) : String :=
  match n with
  | .bvar id name       => s!"{name}.{id}"
  | .mvar id name  => s!"({name}?{id} {bvname})"
  | .nat n         => s!"{n}"
  | .plus n m      => s!"(+ {n.toSygusTerm bvname} {m.toSygusTerm bvname})"
  | .minus n m     => s!"(- {n.toSygusTerm bvname} {m.toSygusTerm bvname})"
  | .mult n m      => s!"(* {n.toSygusTerm bvname} {m.toSygusTerm bvname})"
  | .div n m      => s!"(* {n.toSygusTerm bvname} {m.toSygusTerm bvname})"
  | .pow n m       => s!"(^ {n.toSygusTerm bvname} {m.toSygusTerm bvname})"

def collectMVars : RNat → List (Nat × String)
  | .bvar ..    => []
  | .mvar id nm => [(id, nm.toString)]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectMVars a ++ collectMVars b
  
def collectBVars : RNat → List (Nat × String)
  | .mvar ..    => []
  | .bvar id nm => [(id, nm.toString)]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectBVars a ++ collectBVars b

def toSMTLib (lhs rhs : RNat) : String :=
  let mvars := (lhs.collectMVars ++ rhs.collectMVars).eraseDups
  let decls : String := mvars.map (fun (id,nm) => s!"(declare-const {nm}_{id} Int)") |> String.intercalate "\n"
  let assertion := s!"(assert (= {lhs.toSMTTerm.get!} {rhs.toSMTTerm.get!}))"
  s!"(set-option :model.v2 true)\n{decls}\n{assertion}\n(check-sat)\n(get-model)"

def hasBVar : RNat → Bool
| .bvar ..   => true
| .mvar ..   => false
| .nat ..    => false
| .plus n m  
| .minus n m 
| .mult n m  
| .div n m  
| .pow n m   => hasBVar n || hasBVar m

def toSygus (lhs rhs : RNat) : String :=
  let mvars := (lhs.collectMVars ++ rhs.collectMVars).eraseDups
  let bvars := (lhs.collectBVars ++ rhs.collectBVars).eraseDups
  let bvarnames := bvars.map (fun (id,nm) => s!"{nm}.{id}")
  let bvardecls : String := bvarnames.map (s!"(declare-var {·} Real)")
    |> String.intercalate "\n"
  let bvarargs := bvarnames.map (s!"({·} Real)")
    |> String.intercalate " "
  let natconstraints := ";todo"
  let mvarfuns : String := mvars.map (fun (id,nm) => s!"(synth-fun {nm}?{id} ({bvarargs}) Real)")
    |> String.intercalate "\n"
  let n := bvarnames[0]!
  let constraint := s!"(constraint (= {lhs.toSygusTerm n} {rhs.toSygusTerm n}))"
  s!"
    (set-logic NRA)
    {mvarfuns}
    {bvardecls}
    {natconstraints}
    {constraint}
    (check-synth)
  "




end RNat



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
        args := #["--lang", "sygus2", "--tlimit", "5000"],
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

-- private def s := "
-- (set-option :model.v2 true) (declare-const x_44 Int) (assert (= (+ 5 x_44) 7)) (check-sat) (get-model)
-- "

-- #eval runZ3 s

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

-- #eval runSygus (RNat.toSygus l1 r1)

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
  | .none, s => .error <| .unsolved s

private def parseSygus (s: String) : UnificationResult :=
  let re := re! r"-fun (\w+[\.\?]\d+) .* Real (.*)\)\n"
  let matchs := re.captureAll s
  let names := matchs.filterMap (fun x => (x.get 1) >>= (some ·.toString)) |>.map getMVarId
  let exprs := matchs.filterMap (fun x => (x.get 2) >>= (some ·.toString)) |>.map parseRNatSExpr
  
  if names.size != exprs.size then
    .error <| .unsolved s!"parseSygus: size panic\n{s}"
  else
    names.zipWith f exprs |>.toList |>.mapM id |>.toUnificationResult s!"parseSygus: parsing?\n{s}"
    where
      f : Except String RMVarId → Except String RNat → Option (RMVarId × SubstEnum)
      | .ok id, .ok e => some (id, .nat e)
      | _, _ => none
        
-- #eval parseSygus z



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

