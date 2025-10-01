import Lean.Parser
open Lean

open Std.Internal.Parsec
open Std.Internal.Parsec.String

inductive SExpr where
  | num : Nat → SExpr
  | var : String → SExpr
  | add : SExpr → SExpr → SExpr
  | sub : SExpr → SExpr → SExpr
  | mul : SExpr → SExpr → SExpr
  | div : SExpr → SExpr → SExpr
  deriving Repr

def varName : Parser String := do
  let first ← asciiLetter
  let rest ← many (asciiLetter <|> digit)
  return (first :: rest.toList).asString

partial def sexpr : Parser SExpr := do
  ws
  (numExpr <|> varExpr <|> parenExpr)
where
  numExpr : Parser SExpr := do
    let n ← digits
    return SExpr.num n
  
  varExpr : Parser SExpr := do
    let v ← varName
    return SExpr.var v
  
  parenExpr : Parser SExpr := do
    _ ← pchar '('
    ws
    let op ← pchar '+' <|> pchar '-' <|> pchar '*' <|> pchar '/'
    ws
    let arg1 ← sexpr
    ws
    let arg2 ← sexpr
    ws
    _ ← pchar ')'
    match op with
    | '+' => return SExpr.add arg1 arg2
    | '-' => return SExpr.sub arg1 arg2
    | '*' => return SExpr.mul arg1 arg2
    | '/' => return SExpr.div arg1 arg2
    | _ => fail "unexpected operator"

def parseSExpr (s : String) : Except String SExpr :=
  match sexpr s.mkIterator with
  | .success _ res => Except.ok res
  | .error it err => Except.error s!"Parse error at position {it.i.byteIdx}: {err}"

#eval parseSExpr "42"
#eval parseSExpr "x"
#eval parseSExpr "(+ 1 2)"
#eval parseSExpr "(* (+ 3 4) 5)"
#eval parseSExpr "(- x 10)"
#eval parseSExpr "(/ (* a b) (+ c d))"
