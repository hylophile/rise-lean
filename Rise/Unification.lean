import Rise.Basic
import Lean
import Regex

open Std.Internal.Parsec
  

open IO

unsafe def runZ3 (input : String) : Except Error String :=
  unsafeIO do
    let child ← do
      let (stdin, child) ← (← IO.Process.spawn {
        cmd := "z3",
        args := #["-in"],
        stdin := .piped,
        stdout := .piped,
        stderr := .null
      }).takeStdin

      stdin.putStrLn input
      pure child
    child.stdout.readToEnd

def s := "(set-option :model.v2 true) (declare-const x_44 Int) (assert (= (+ 5 x_44) 7)) (check-sat) (get-model)"

#eval runZ3 s

def l : RNat := .plus (.nat 5) (.mvar 55 `x)
def r : RNat := .nat 7

#eval "(-5)".toNat?

def parseArrowFormat (input : String) : Option Substitution := do
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
          | none => none
        | none => none
      | _ => continue
    
    some result
  | _ => none

-- #eval parseArrowFormat "sat\nx_55 -> 5\ny_59 -> 8"

unsafe def runSygus (input : String) : Except Error (String × String) :=
  dbg_trace input
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

def l1 : RNat := .plus (.nat 5) (.mvar 55 `x)
def r1 : RNat := .bvar 23 `z

#eval runSygus (RNat.toSygus l1 r1)

unsafe def solveWithZ3 (l r : RNat) : Option Substitution :=
  let smtlib := RNat.toSMTLib l r
  match runZ3 smtlib with
  | .ok s =>  
    dbg_trace (smtlib,s)
    parseArrowFormat s
  | _ => .none

unsafe def solveWithSygus (l r : RNat) : Option Substitution :=
  let s := RNat.toSygus l r
  match runSygus s with
  | .ok s =>
    parseSygus s
  | _ => .none

unsafe def solve (l r : RNat) : Option Substitution :=
  if l.hasBVar || r.hasBVar then
    solveWithSygus l r
  else
    solveWithZ3 l r


unsafe def s3 (smtlib : String) : Option Substitution :=
  match runZ3 smtlib with
  | .ok s =>  
    parseArrowFormat s
  | _ => .none

def z := "


(
(define-fun p_3 ((q Real)) Real (- 1))
(define-fun r_5 ((q Real)) Real (+ 5))
)  
"

def parseSygus (s: String) : Option Substitution :=
  let re := re! r"-fun (\w+) .* Real (.*)\)\n"
  let matchs := re.captureAll s
  let names := matchs.filterMap (fun x => (x.get 1) >>= (some ·.toString))
  let exprs := matchs.filterMap (fun x => (x.get 2) >>= (some ·.toString))
  
  dbg_trace names.zip exprs
  none

#eval parseSygus z



-- #eval solveWithZ3 l r
-- #eval s3 s


-- unification algorithm adapted from
-- https://web.archive.org/web/20250713140859/http://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm

-- we could throw errors here instead of just Option

mutual
unsafe def unifyOneRNat (s t : RNat) : Option Substitution :=
  match s, t with
  | .nat n, .nat m =>
    if n == m then return [] else none

  | .bvar x _, .bvar y _ =>
    if x == y then some [] else none

  | .mvar x _, .mvar y _ =>
    if x == y then some [] else some [(x, .nat t)]

  | .mvar x _, term | term, .mvar x _ =>
    if term.has x then
      none
    else
      some [(x, .nat term)]

  -- | .plus n1 m1, .plus n2 m2 =>
  --   unifyRNat [(n1, n2), (m1, m2)]

  -- | .minus n1 m1, .minus n2 m2 =>
  --   unifyRNat [(n1, n2), (m1, m2)]

  -- | .mult n1 m1, .mult n2 m2 =>
  --   unifyRNat [(n1, n2), (m1, m2)]

  | _, _ => do
    let x := solveWithZ3 s t --(RNat.toSMTLib s t)
    x
    -- dbg_trace x
    -- none

unsafe def unifyRNat (equations : List (RNat × RNat)) : Option Substitution :=
  match equations with
  | [] => some []
  | (x, y) :: rest => do
    let tailSubst <- unifyRNat rest
    let x' <- x.apply tailSubst
    let y' <- y.apply tailSubst
    let headSubst <- unifyOneRNat x' y'
    headSubst ++ tailSubst
end

-- TODO think about corresponding structural rules
-- TODO relate eqsat and unifi

mutual
unsafe def unifyOneRData (s t : RData) : Option Substitution :=
  match s, t with
  | .mvar x _, .mvar y _ =>
    if x == y then some [] else some [(x, .data t)]

  | .mvar x _, term | term, .mvar x _ =>
    if term.has x then
      none
    else
      some [(x, .data term)]

  | .bvar n1 _, .bvar n2 _ =>
    if n1 == n2 then some [] else none

  | .array k1 d1, .array k2 d2 =>
    match unifyRNat [(k1, k2)], unifyRData [(d1, d2)] with
    | some s1, some s2 => s1 ++ s2
    | _, _ => none

  | .pair l1 r1, .pair l2 r2 =>
    unifyRData [(l1, l2), (r1, r2)]

  | .index k1, .index k2 =>
    unifyOneRNat k1 k2

  | .scalar x, .scalar y => if x == y then some [] else none

  | .natType, .natType => some []

  | .vector k1 d1, .vector k2 d2 =>
    match unifyRNat [(k1, k2)], unifyRData [(d1, d2)] with
    | some s1, some s2 => s1 ++ s2
    | _, _ => none

  | _, _ => none

unsafe def unifyRData (equations : List (RData × RData)) : Option Substitution :=
  match equations with
  | [] => some []
  | (x, y) :: t => do
    let t2 <- unifyRData t
    let t1 <- unifyOneRData (x.apply t2) (y.apply t2)
    t1 ++ t2
end

partial def RData.unify (l r : RData) : Option Substitution :=
  let result := unify l r
  result

mutual
unsafe def unifyOneRType (s t : RType) : Option Substitution :=
  match s, t with
  | .data dt1, .data dt2 =>
    unifyRData [(dt1, dt2)]

  | .pi bk1 pc1 un1 body1, .pi bk2 pc2 un2 body2 =>
    if bk1 == bk2 && pc1 == pc2 && un1 == un2 then
      unifyRType [(body1, body2)]
    else
      none

  | .fn binderType1 body1, .fn binderType2 body2 =>
    unifyRType [(binderType1, binderType2), (body1, body2)]

  | _, _ => none

unsafe def unifyRType (equations : List (RType × RType)) : Option Substitution :=
  match equations with
  | [] => some []
  | (x, y) :: rest => do
    let tailSubst <- unifyRType rest
    let x' <- x.apply tailSubst
    let y' <- y.apply tailSubst
    let headSubst <- unifyOneRType x' y'
    headSubst ++ tailSubst
end

unsafe def RType.unify (l r : RType) : Option Substitution :=
  unifyRType [(l, r)]

-- def Substitution.toString (s : Substitution) : String :=
--   let pairs := s.map (fun (id, term) => s!"({id} -> {repr term})")
--   "[" ++ String.intercalate ", " pairs ++ "]"

-- instance : ToString Substitution where
--   toString := Substitution.toString

unsafe def unify := RType.unify


-- technically, the "_, _" case doesn't check for enough. we would want better checking here, but we trust the algorithm.
private unsafe def unifies (l r : RType) : Bool :=
  match l.unify r, r.unify l with
  | some s1, some s2 =>
    -- dbg_trace s1
    -- dbg_trace s2
    -- dbg_trace (l.apply s1, r.apply s1)
    -- dbg_trace (l.apply s2, r.apply s2)
    -- dbg_trace (l.apply s1 == r.apply s1)
    -- dbg_trace (l.apply s2 == r.apply s2)
    l.apply s1 == r.apply s1 && l.apply s2 == r.apply s2
  | _, _ =>
    -- dbg_trace (l.unify r, r.unify l)
    false

-- /--
--   Utility elaborator for Rise Types - adds metavariables to context.
--   "[Rise Type with <identifiers> | <rise_type>]"

--   TODO (if necessary): make a difference between variables and metavariables.
--   TODO (if necessary): currently all metavars are just data
-- -/
-- elab "[RTw" mvars:ident* "|" t:rise_type "]" : term => do
--   let l ← Lean.Elab.liftMacroM <| Lean.expandMacros t
--   let mvars ← mvars.toList.mapM (fun var => do
--     return {userName := var.getId, kind := RKind.data, type:= none}
--   )
--   -- let mvars : List ((Lean.Name × RKind × Option RType) × Nat) := mvars.zipIdx
--   let mvars : Lean.PersistentHashMap RMVarId MetaVarDeclaration :=
--     mvars.zipIdx.foldl (λ acc (x, id) => acc.insert id x) Lean.PersistentHashMap.empty
--   liftToTermElabMWith defaultContext {defaultState with mvars := mvars} <| elabRType l


-- #check [RTw a     | a                     ]
-- tests. note that both params to unify should have the same mvar context.

-- #assert (unifies [RTw a     | a                     ] [RTw a     | scalar                ]) == true
-- #assert (unifies [RTw a     | scalar                 ] [RTw a     | a                    ]) == true
-- #assert (unifies [RTw a     | a                     ] [RTw a     | a                    ]) == true
-- #assert (unifies [RTw a     | 3·a                 ] [RTw a     | 3·scalar            ]) == true
-- #assert (unifies [RTw a     | scalar → a             ] [RTw a     | scalar → 3<scalar>     ]) == true
-- #assert (unifies [RTw a     | 4·a                 ] [RTw a     | 4·5<scalar>         ]) == true
-- #assert (unifies [RTw a b   | a                     ] [RTw a b   | b                    ]) == true
-- #assert (unifies [RTw a b   | a × b                 ] [RTw a b   | scalar × 5<scalar>     ]) == true
-- #assert (unifies [RTw a b   | scalar × a             ] [RTw a b   | b × 3<scalar>         ]) == true
-- #assert (unifies [RTw a b   | a × b                 ] [RTw a b   | 5<scalar> × scalar     ]) == true
-- #assert (unifies [RTw a b   | 5<scalar> × scalar      ] [RTw a b   | a × b                ]) == true
-- #assert (unifies [RTw a b   | a → a                 ] [RTw a b   | a → b                ]) == true
-- #assert (unifies [RTw a b c | a → b                 ] [RTw a b c | b → c                ]) == true
-- #assert (unifies [RTw a b c | a → b                 ] [RTw a b c | c → c                ]) == true
-- #assert (unifies [RTw a b c | a × b                 ] [RTw a b c | c                    ]) == true
-- #assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → scalar            ]) == true
-- #assert (unifies [RTw a b c | c → scalar             ] [RTw a b c | a × b → a            ]) == true
-- #assert (unifies [RTw a b c | a × b                 ] [RTw a b c | b × c                ]) == true
-- #assert (unifies [RTw a b c | b × c                 ] [RTw a b c | a × b                ]) == true
-- #assert (unifies [RTw       | 2·scalar             ] [RTw       | 3·scalar            ]) == false
-- #assert (unifies [RTw       | scalar                 ] [RTw       | 3<scalar>             ]) == false
-- #assert (unifies [RTw       | idx[1]                ] [RTw       | idx[2]               ]) == false
-- #assert (unifies [RTw a     | scalar → scalar         ] [RTw a     | a                    ]) == false
-- #assert (unifies [RTw a     | a                     ] [RTw a     | a → scalar            ]) == false
-- #assert (unifies [RTw a     | a → scalar             ] [RTw a     | a                    ]) == false
-- #assert (unifies [RTw a     | a                     ] [RTw a     | a × scalar            ]) == false
-- #assert (unifies [RTw a     | a × scalar             ] [RTw a     | a                    ]) == false
-- #assert (unifies [RTw a b   | a                     ] [RTw a b   | a → b                ]) == false
-- #assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → c                ]) == false
-- #assert (unifies [RTw a b c | c → c                 ] [RTw a b c | a × b → a            ]) == false
-- -- these mvars are of kind nat, but no one checked if they fit! these shouldn't succeed right now.
-- #assert (unifies [RTw a     | idx[a]                ] [RTw a     | idx[5]               ]) == true
-- #assert (unifies [RTw a b   | a·b                 ] [RTw a b   | 3·scalar            ]) == true
-- #assert (unifies [RTw a b   | a·a                 ] [RTw a b   | 3·b                ]) == true
-- #assert (unifies [RTw a b   | idx[a]                ] [RTw a b   | idx[b]               ]) == true




-- #eval (unify [RTw a     | idx[a]                ] [RTw a     | idx[5]               ])
