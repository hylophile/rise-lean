import Rise.Basic
import Rise.Unification.SymPy.Parse
import Rise.Unification.MVars
import Lean


private def RNat.toSympyString : RNat → String :=
    let rec go : RNat → String
      | .bvar id name => bvarToString id name.toString
      | .mvar id name => mvarToString id name.toString
      | .nat n => s!"{n}"
      | .plus n m => s!"({go n}+{go m})"
      | .minus n m => s!"({go n}-{go m})"
      | .mult n m => s!"({go n}*{go m})"
      | .div n m => s!"({go n}/{go m})"
      | .pow n m => s!"({go n}**{go m})"
    go

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
res = sp.solvers.solve(({eqsolves},), ({mvarsolves},), dict=True)
if len(res) != 1:
  raise ValueError('did not find unique solution!')
print(res[0])
  "

private def l1 : RNat := .plus (.nat 5) (.mvar 55 `x)
private def r1 : RNat := .bvar 23 `z

open IO
private unsafe def runSymPyImpl (input : String) : Except Error (String × String) :=
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

@[implemented_by runSymPyImpl]
opaque runSymPy (input : String) : Except Error (String × String)


private def pairToSubstitution (ps : List (RNat × RNat)) : Option Substitution :=
  ps |>.mapM (fun (x,v) => match x with
    | .mvar id _ => some (id, .nat v)
    | _ => none)

def solveWithSymPy (eqs: List (RNat × RNat)) : RElabM Substitution :=
  if eqs.length == 0 then return [] else
  let sympyInput := eqs |> listToSymPyProgram
  dbg_trace s!"sympy_input:\n{sympyInput}\n\n"
  match sympyInput |> runSymPy with
  | .ok (stdout,_stderr) => do
    let res ← elabSymPySolveOutput stdout
    match res with
    | .ok res =>
      match res |> pairToSubstitution with
      | some res => return res
      | none => throwError "failure"
    | .error err => throwError s!"solving with sympy failed:\n{err}\ninput was:\n{sympyInput}"
  | .error e => throwError e.toString

-- #eval IO.print <|listToSymPyProgram [(l1, r1)]
-- #eval runSymPy <| listToSymPyProgram [(l1, r1)]
