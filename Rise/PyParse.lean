import Lean
import Rise.RElabM

open Lean Parser Elab Command Meta
-- {Symbol('m_n_12', integer=True, positive=True): Add(Symbol('b_h_1', integer=True, positive=True), Integer(3)), Symbol('m_n_6', integer=True, positive=True): Add(Symbol('b_w_0', integer=True, positive=True), Integer(3)), Symbol('m_n_60', integer=True, positive=True): Add(Mul(Rational(1, 2), Symbol('b_h_1', integer=True, positive=True)), Integer(2)), Symbol('m_n_61', integer=True, positive=True): Add(Mul(Rational(1, 2), Symbol('b_w_0', integer=True, positive=True)), Integer(2))}
-- 

declare_syntax_cat sympy_symb
syntax "Symbol(" ident "," "integer=True," "positive=True)" : sympy_symb

declare_syntax_cat sympy_expr
syntax sympy_symb : sympy_expr

declare_syntax_cat sympy_pair
syntax sympy_symb ":" sympy_expr : sympy_pair

declare_syntax_cat sympy_map
syntax (sympy_pair,*,?) : sympy_map

unsafe def parseSymPyOutput (s : String) : TermElabM Syntax := do
  let env ← getEnv
  let stxExcept := Parser.runParserCategory env `sympy_map s
  match stxExcept with
  | .ok stx => pure stx
  | .error err => throwError "parse error: {err}"

def elabSymPySymb : Syntax → RElabM RNat
  | `(sympy_symb| Symbol($x:ident, integer=True, positive=True)) =>
    match x.getId.toString.split (· == '_') with
    | ["m",n,id] => match id.toNat? with
      | some id => return RNat.mvar id n.toName
      | none => throwUnsupportedSyntax
    | ["b",n,id] => match id.toNat? with
      | some id => return RNat.bvar id n.toName
      | none => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

def elabSymPyExpr : Syntax → RElabM RNat
  | `(sympy_expr| $s:sympy_symb) => elabSymPySymb s
  | _ => throwUnsupportedSyntax

def elabSymPyPair : Syntax → RElabM (RNat × RNat)
  | `(sympy_pair| $s:sympy_symb : $e:sympy_expr) => do
    let s ← elabSymPySymb s
    let e ← elabSymPyExpr e
    return (s,e)
  | _ => throwUnsupportedSyntax


def elabFromSymPyToRNat : Syntax → RElabM (List (RNat × RNat))
  | `(sympy_map| $p:sympy_pair,*) => do
    let ps ← p.getElems.raw.mapM (fun x => elabSymPyPair x)
    return ps.toList
  | _ => throwUnsupportedSyntax


unsafe def el : RElabM (List (RNat × RNat)) := do
    -- removed single quotes ''
    -- let stx ← parseSymPyOutput "Symbol(m_n_12, integer=True, positive=True): Add(Symbol(b_h_1, integer=True, positive=True), Integer(3)), Symbol(m_n_6, integer=True, positive=True): Add(Symbol(b_w_0, integer=True, positive=True), Integer(3)), Symbol(m_n_60, integer=True, positive=True): Add(Mul(Rational(1, 2), Symbol(b_h_1, integer=True, positive=True)), Integer(2)), Symbol(m_n_61, integer=True, positive=True): Add(Mul(Rational(1, 2), Symbol(b_w_0, integer=True, positive=True)), Integer(2))"
    -- let stx ← parseSymPyOutput "Symbol(m_n_12, integer=True, positive=True)"
    let stx ← parseSymPyOutput "Symbol(m_n_12, integer=True, positive=True):Symbol(m_n_12, integer=True, positive=True),Symbol(m_n_12, integer=True, positive=True):Symbol(m_n_12, integer=True, positive=True),Symbol(m_np_1200, integer=True, positive=True):Symbol(m_nnnnn_2, integer=True, positive=True)"
    let stx ← liftMacroM <| expandMacros stx
    let rnat ← elabFromSymPyToRNat stx
    -- Pretty-print syntax as Lean code
    -- IO.println s!"Pretty syntax: {stx.prettyPrint}"
    -- -- Or raw structure representation
    -- IO.println s!"Raw structure: {toString stx}"
    return rnat

-- elab "[RiseTE|" e:sympy_output "]" : term => unsafe do
--   let x <- el e
--   let p ← liftMacroM <| expandMacros e
--   liftToTermElabM <| p

#eval liftToTermElabM el
