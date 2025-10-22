import Rise.Basic
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

def collectMVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectMVars ++ r.collectMVars) |> List.flatten

def collectBVars (eqs : List (RNat × RNat)) : List String :=
  eqs.map (fun (l,r) => l.collectBVars ++ r.collectBVars) |> List.flatten

def listToSymPyProgram (eqs : List (RNat × RNat)) : String :=
  let mvars := (collectMVars eqs).eraseDups
  let bvars := (collectBVars eqs).eraseDups
  let vars := mvars ++ bvars
  let varidents := vars |> String.intercalate ", "
  let varnames := vars |> String.intercalate " "
  let eqms := eqs.mapIdx (fun idx (l,r) =>
      let eqstr := s!"eq{idx} = Equality({l.toSympyString}, {r.toSympyString})"
      let mvars := (l.collectMVars ++ r.collectMVars).eraseDups
      let mvarsstr := mvars |> String.intercalate ", "
      (eqstr, mvarsstr, idx, mvars.length)
    )
  let eqdefs := eqms.map (fun (e,_,_,_) => e) |> String.intercalate "\n"
  let eqsolves := eqms.map (fun (_,_,idx,_) => s!"eq{idx}") |> String.intercalate ", "
  let mvarsolves := mvars |> String.intercalate ", "
  s!"
from sympy import Eq, Equality, symbols
from sympy.solvers import solve
{varidents} = symbols(\"{varnames}\", integer=True, positive=True)
{eqdefs}
res = solve(({eqsolves}), ({mvarsolves}))
print(res) 
  "

def pairToSymPyProgram (lhs rhs : RNat) : String :=
  let mvars := (lhs.collectMVars ++ rhs.collectMVars).eraseDups
  let bvars := (lhs.collectBVars ++ rhs.collectBVars).eraseDups
  let vars := mvars ++ bvars
  let varidents := vars |> String.intercalate ", "
  let varnames := vars |> String.intercalate " "
  if mvars.length < 1 then "" else
  s!"
from sympy import Eq, Equality, symbols
from sympy.solvers import solve
{varidents} = symbols(\"{varnames}\", integer=True, positive=True)
eq1 = Equality({lhs.toSympyString}, {rhs.toSympyString})
res = solve(eq1, {mvars[0]!})
print(res) 
  "

private def l1 : RNat := .plus (.nat 5) (.mvar 55 `x)
private def r1 : RNat := .bvar 23 `z

#eval IO.print <| pairToSymPyProgram l1 r1

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

#eval IO.print <|listToSymPyProgram [(l1, r1)]
#eval runSymPy <| listToSymPyProgram [(l1, r1)]
