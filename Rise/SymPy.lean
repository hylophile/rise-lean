import Rise.Basic
import Rise.SymPyParse
import Lean

def mvarToString : Nat → String → String
  | id, nm => s!"m_{nm}_{id}"
def bvarToString : Nat → String → String
  | id, nm => s!"b_{nm}_{id}"


private def RNat.collectMVars : RNat → List String
  | .bvar ..    => []
  | .mvar id nm => [mvarToString id nm.toString]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectMVars a ++ collectMVars b
  
private def RNat.collectBVars : RNat → List String
  | .mvar ..    => []
  | .bvar id nm => [bvarToString id nm.toString]
  | .nat _      => []
  | .plus a b
  | .minus a b
  | .mult a b
  | .div a b
  | .pow a b    => collectBVars a ++ collectBVars b

private def RNat.toSympyString : RNat → String :=
    let rec go : RNat → String
      | .bvar id name => bvarToString id name.toString
      | .mvar id name => mvarToString id name.toString
      | .nat n => s!"{n}"
      | .plus n m => s!"({go n}+{go m})"
      | .minus n m => s!"({go n}-{go m})"
      | .mult n m => s!"({go n}*{go m})"
      | .div n m => s!"({go n}/{go m})"
      | .pow n m => s!"({go n}^{go m})"
    go

private def collectMVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectMVars ++ r.collectMVars) |> List.flatten

private def collectBVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectBVars ++ r.collectBVars) |> List.flatten

private def listToSymPyProgram (eqs : List (RNat × RNat)) : String :=
  let mvars := (collectMVars eqs).eraseDups
  let bvars := (collectBVars eqs).eraseDups
  let vars := mvars ++ bvars
  let varidents := vars |> String.intercalate ", "
  let varnames := vars |> String.intercalate " "
  let eqms := eqs.mapIdx (fun idx (l,r) =>
      let eqstr := s!"eq{idx} = sp.Equality({l.toSympyString}, {r.toSympyString})"
      let mvars := (l.collectMVars ++ r.collectMVars).eraseDups
      let mvarsstr := mvars |> String.intercalate ", "
      (eqstr, mvarsstr, idx, mvars.length)
    )
  let eqdefs := eqms.map (fun (e,_,_,_) => e) |> String.intercalate "\n"
  let eqsolves := eqms.map (fun (_,_,idx,_) => s!"eq{idx}") |> String.intercalate ", "
  let mvarsolves := mvars |> String.intercalate ", "
  s!"
import sympy as sp
{varidents} = sp.symbols(\"{varnames}\", integer=True, positive=True)
{eqdefs}
res = sp.solvers.solve(({eqsolves},), ({mvarsolves},))
print(res)
  "

private def l1 : RNat := .plus (.nat 5) (.mvar 55 `x)
private def r1 : RNat := .bvar 23 `z

open IO
private unsafe def runSymPy (input : String) : Except Error (String × String) :=
  unsafeIO do
    let child ← do
      let (stdin, child) ← (← IO.Process.spawn {
        cmd := "uv",
        args := #["run" ,"--with", "sympy", "-"],
        stdin := .piped,
        stdout := .piped,
        stderr := .piped
      }).takeStdin

      stdin.putStrLn input
      pure child
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    return (stdout, stderr)

private def pairToSubstitution (ps : List (RNat × RNat)) : Option Substitution :=
  ps |>.mapM (fun (x,v) => match x with
    | .mvar id _ => some (id, .nat v)
    | _ => none)

unsafe def solveWithSymPy (eqs: List (RNat × RNat)) : RElabM Substitution :=
  if eqs.length == 0 then return [] else
  match eqs |> listToSymPyProgram |> runSymPy with
  | .ok (stdout,_stderr) => do
    let res := (← elabSymPySolveOutput stdout) |> pairToSubstitution
    match res with
    | some res => return res
    | none => throwError "failure"
  | .error e => throwError e.toString

-- #eval IO.print <|listToSymPyProgram [(l1, r1)]
-- #eval runSymPy <| listToSymPyProgram [(l1, r1)]
