import Lean
import Rise.RElabM

open Lean Parser Elab Command Meta

declare_syntax_cat sympy_symb
syntax ident : sympy_symb

declare_syntax_cat sympy_expr
syntax sympy_symb : sympy_expr
syntax num : sympy_expr
syntax:10 sympy_expr:10 "+" sympy_expr:11  : sympy_expr
syntax:10 sympy_expr:10 "-" sympy_expr:11  : sympy_expr
syntax:20 sympy_expr:20 "*" sympy_expr:21  : sympy_expr
syntax:20 sympy_expr:20 "/" sympy_expr:21  : sympy_expr
syntax    "(" sympy_expr ")"             : sympy_expr

declare_syntax_cat sympy_pair
syntax sympy_symb ":" sympy_expr : sympy_pair

declare_syntax_cat sympy_map
syntax "{" (sympy_pair,*,?) "}": sympy_map


private def elabSymPySymb : Syntax → RElabM RNat
  | `(sympy_symb| $x:ident) =>
    match x.getId.toString.split (· == '_') with
    | ["m",n,id] => match id.toNat? with
      | some id => return RNat.mvar id n.toName
      | none => throwUnsupportedSyntax
    | ["b",n,id] => match id.toNat? with
      | some id => return RNat.bvar id n.toName
      | none => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

private partial def elabSymPyExpr : Syntax → RElabM RNat
  | `(sympy_expr| ($e:sympy_expr)) => elabSymPyExpr e
  | `(sympy_expr| $s:sympy_symb) => elabSymPySymb s
  | `(sympy_expr| $n:num) => do
    let n := n.getNat
    return RNat.nat n
  | `(sympy_expr| $l:sympy_expr + $r:sympy_expr) => do
    let l ← elabSymPyExpr l
    let r ← elabSymPyExpr r
    return RNat.plus l r
  | `(sympy_expr| $l:sympy_expr - $r:sympy_expr) => do
    let l ← elabSymPyExpr l
    let r ← elabSymPyExpr r
    return RNat.minus l r
  | `(sympy_expr| $l:sympy_expr * $r:sympy_expr) => do
    let l ← elabSymPyExpr l
    let r ← elabSymPyExpr r
    return RNat.mult l r
  | `(sympy_expr| $l:sympy_expr / $r:sympy_expr) => do
    let l ← elabSymPyExpr l
    let r ← elabSymPyExpr r
    return RNat.div l r

  | _ => throwUnsupportedSyntax

private def elabSymPyPair : Syntax → RElabM (RNat × RNat)
  | `(sympy_pair| $s:sympy_symb : $e:sympy_expr) => do
    let s ← elabSymPySymb s
    let e ← elabSymPyExpr e
    return (s,e)
  | _ => throwUnsupportedSyntax

private def elabSymPyMap : Syntax → RElabM (List (RNat × RNat))
  | `(sympy_map| {$p:sympy_pair,*}) => do
    let ps ← p.getElems.raw.mapM (fun x => elabSymPyPair x)
    return ps.toList
  | _ => throwUnsupportedSyntax

private def parseSymPyMap (s : String) : TermElabM (Except String Syntax) := do
  let env ← getEnv
  let stxExcept := Parser.runParserCategory env `sympy_map s
  match stxExcept with
  | .ok stx => return .ok stx
  | .error err => return .error s!"sympy parse error: {err}\ninput: '{s}'"

def elabSymPySolveOutput (s : String) : RElabM (Except String (List (RNat × RNat))) := do
    let stx ← parseSymPyMap s
    match stx with
    | .ok stx =>
      let stx ← liftMacroM <| expandMacros stx
      let rnats ← elabSymPyMap stx
      return .ok rnats
    | .error err => return .error err

-- #eval liftToTermElabM <| elabSymPySolveOutput "{m_n_12: b_h_1 + 3, m_n_6: b_w_0 - 3, m_n_60: b_h_1/2 + 2, m_n_61: b_w_0/2 + 2}"
