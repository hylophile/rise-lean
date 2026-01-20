import Rise.Basic
import Rise.Unification.MVars


def RData.getNatEquivs (l:RData) (r:RData) : List (RNat × RNat) :=
  match l,r with
  | .array n1 d1 , .array n2 d2  => (n1, n2) :: d1.getNatEquivs d2
  | .pair l1 l2  , .pair r1 r2   => l1.getNatEquivs r1 ++ l2.getNatEquivs r2
  | .index n1    , .index n2     => [(n1, n2)]
  | .vector n1 d1, .vector n2 d2 => (n1, n2) :: d1.getNatEquivs d2
  | _,_ => []

def RType.getNatEquivs (l:RType) (r:RType) : List (RNat × RNat) :=
  match l,r with
  | .data l, .data r => l.getNatEquivs r
  | .pi _ _ _ l, .pi _ _ _ r => l.getNatEquivs r
  | .fn l1 l2, .fn r1 r2 => l1.getNatEquivs r1 ++ l2.getNatEquivs r2
  | _, _ => []

private def RNat.toSmtSExpr : RNat → String
  | .bvar idx name => s!"b_{sane name}_{idx}"
  | .mvar id name => s!"m_{sane name}_{id}"
  | .nat n => s!"{n}"
  | .plus n m => s!"(+ {n.toSmtSExpr} {m.toSmtSExpr})"
  | .minus n m => s!"(- {n.toSmtSExpr} {m.toSmtSExpr})"
  | .mult n m => s!"(* {n.toSmtSExpr} {m.toSmtSExpr})"
  | .div n m => s!"(div {n.toSmtSExpr} {m.toSmtSExpr})"
  | .pow n m => s!"(^ {n.toSmtSExpr} {m.toSmtSExpr})"

private def RData.toSmtSExpr : RData → String
  | .bvar idx name => s!"b_{sane name}_{idx}"
  | .mvar id name => s!"m_{sane name}_{id}"
  | .array n d     => s!"(array {n.toSmtSExpr} {d.toSmtSExpr})"
  | .pair d1 d2    => s!"(pair {d1.toSmtSExpr} {d2.toSmtSExpr})"
  | .index n       => s!"(index {n.toSmtSExpr})"
  | .scalar x      => s!"{x}"
  | .natType       => "natType"
  | .vector n d    => s!"(vector {n.toSmtSExpr} {d.toSmtSExpr})"

private def RType.toSmtSExpr : RType → String
  | .data dt => dt.toSmtSExpr
  | .pi kind _pc un body => s!"(pi {un} {kind} {body.toSmtSExpr})"
  | .fn binderType body => s!"(-> {binderType.toSmtSExpr} {body.toSmtSExpr})"

private def RNat.getDivs (n : RNat) : List (RNat × RNat) :=
  match n with
  | .plus n m  => n.getDivs ++ m.getDivs
  | .minus n m => n.getDivs ++ m.getDivs
  | .mult n m  => n.getDivs ++ m.getDivs
  | .div n m   => [(n,m)] ++ n.getDivs ++ m.getDivs
  | .pow n m   => n.getDivs ++ m.getDivs
  | _ => []


def mkSmtCheck (appliedGoals : List (RType × RType)) : String :=
  let natEquivs := appliedGoals.map (fun (l,r) => RType.getNatEquivs l r)
    |>.flatten
    |>.eraseDups
  let vars := collectVars natEquivs
    |>.map (fun s => s!"(declare-const {s} Int)\n(assert (> {s} 0))\n")
    |> String.intercalate "\n"
  let divs := natEquivs.map (fun (l,r) => l.getDivs ++ r.getDivs)
    |>.flatten
    |>.eraseDups
    |>.map (fun (l,r) => s!"(assert (= 0 (mod {l.toSmtSExpr} {r.toSmtSExpr})))")
    |> String.intercalate "\n"
  let asserts := natEquivs
    |>.map (fun (l,r) => s!"(assert (= {l.toSmtSExpr} {r.toSmtSExpr}))")
    |> String.intercalate "\n"
  s!"
{vars}
{asserts}
{divs}
(check-sat)
(get-model)
  "

