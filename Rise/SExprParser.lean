import Lean.Parser
import Rise.Basic

open Lean

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def varName : Parser String := do
  let first ← asciiLetter
  let rest ← many (asciiLetter <|> digit)
  return (first :: rest.toList).asString

partial def sexpr : Parser RNat := do
  ws
  (numExpr <|> varExpr <|> parenExpr)
where
  numExpr : Parser RNat := do
    let n ← digits
    return RNat.nat n
  
  varExpr : Parser RNat := do
    let v ← varName
    let sep ← pchar '.' <|> pchar '?'
    
    let id ← digits
    if sep == '.' then
     return RNat.bvar id v.toName
    else
     return RNat.mvar id v.toName


 
  parenExpr : Parser RNat := do
    _ ← pchar '('
    ws   
    let signedNum? ← optional do
      let sign ← pchar '-' <|> pchar '+'
      ws
      let n ← digits
      return (sign, n)

    match signedNum? with
    | some (sign, n) =>
        ws
        _ ← pchar ')'
        if sign = '-' then
          return RNat.minus (RNat.nat 0) (RNat.nat n)
        else
          return RNat.nat n
    | none =>
      let op ← pchar '+' <|> pchar '-' <|> pchar '*' <|> pchar '/'
      ws
      let arg1 ← sexpr
      ws
      let arg2 ← sexpr
      ws
      _ ← pchar ')'
      match op with
      | '+' => return RNat.plus arg1 arg2
      | '-' => return RNat.minus arg1 arg2
      | '*' => return RNat.mult arg1 arg2
      | '/' => return RNat.div arg1 arg2
      | _ => fail "unexpected operator"

def parseRNatSExpr (s : String) : Except String RNat :=
  match sexpr s.mkIterator with
  | .success _ res => Except.ok res
  | .error it err => Except.error s!"Parse error at position {it.i.byteIdx}: {err}"

-- #eval parseRNatSExpr "42"
-- #eval parseRNatSExpr "x"
-- #eval parseRNatSExpr "(+ 1 2)"
-- #eval parseRNatSExpr "(* (+ 3 4) 5)"
-- #eval parseRNatSExpr "(- xyz?505 10)"
-- #eval parseRNatSExpr "(/ (* a b) (+ c d))"
