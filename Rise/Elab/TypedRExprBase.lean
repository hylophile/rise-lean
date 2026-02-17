import Rise.Basic
import Rise.Elab.Type
import Lean
open Lean

instance : ToExpr RLit where
  toExpr
    | .bool b => mkAppN (mkConst ``RLit.bool) #[toExpr b]
    | .int i => mkAppN (mkConst ``RLit.int) #[toExpr i]
    | .float f => mkAppN (mkConst ``RLit.float) #[toExpr f]
  toTypeExpr := mkConst ``RLit

instance : ToExpr RNat2Nat where
  toExpr v := mkAppN (mkConst ``RNat2Nat.mk) #[toExpr v.binderName, toExpr v.body]
  toTypeExpr := mkConst ``RNat2Nat

instance : ToExpr RNat2Data where
  toExpr v := mkAppN (mkConst ``RNat2Data.mk) #[toExpr v.binderName, toExpr v.body]
  toTypeExpr := mkConst ``RNat2Data

instance : ToExpr RWrapper where
  toExpr
    | .nat b => mkAppN (mkConst ``RWrapper.nat) #[toExpr b]
    | .data i => mkAppN (mkConst ``RWrapper.data) #[toExpr i]
    | .nat2nat v => toExpr v
    | .nat2data v => toExpr v
    | .addrSpace a => mkAppN (mkConst ``RWrapper.addrSpace) #[toExpr a]
  toTypeExpr := mkConst ``RWrapper

mutual
partial
def TypedRExpr.toExpr (e : TypedRExpr) : Expr  :=
    let nodeExpr := e.node.toExpr
    let typeExpr := ToExpr.toExpr e.type
    mkAppN (mkConst ``TypedRExpr.mk) #[nodeExpr, typeExpr]

partial
def TypedRExprNode.toExpr : TypedRExprNode → Expr
    | .lit n =>
        mkAppN (mkConst ``TypedRExprNode.lit) #[toExpr n]
    | .bvar index name =>
        mkAppN (mkConst ``TypedRExprNode.bvar) #[mkNatLit index, toExpr name]
    | .const name =>
        mkAppN (mkConst ``TypedRExprNode.const) #[toExpr name]
    | .lam name t body =>
        mkAppN (mkConst ``TypedRExprNode.lam) #[toExpr name, toExpr t, body.toExpr]
    | .deplam name kind body =>
        mkAppN (mkConst ``TypedRExprNode.deplam) #[toExpr name, toExpr kind, body.toExpr]
    | .app e1 e2 =>
        mkAppN (mkConst ``TypedRExprNode.app) #[e1.toExpr, e2.toExpr]
    | .depapp e1 e2 =>
        mkAppN (mkConst ``TypedRExprNode.depapp) #[e1.toExpr, toExpr e2]
end

instance : ToExpr TypedRExpr where
  toExpr := TypedRExpr.toExpr
  toTypeExpr := mkConst ``TypedRExpr

instance : ToExpr TypedRExprNode where
  toExpr := TypedRExprNode.toExpr
  toTypeExpr := mkConst ``TypedRExprNode

declare_syntax_cat rise_expr_numlit_suffix
syntax "int" : rise_expr_numlit_suffix
syntax "i8"  : rise_expr_numlit_suffix
syntax "i16" : rise_expr_numlit_suffix
syntax "i32" : rise_expr_numlit_suffix
syntax "i64" : rise_expr_numlit_suffix
syntax "u8"  : rise_expr_numlit_suffix
syntax "u16" : rise_expr_numlit_suffix
syntax "u32" : rise_expr_numlit_suffix
syntax "u64" : rise_expr_numlit_suffix


declare_syntax_cat rise_expr_scilit_suffix
syntax "float" : rise_expr_scilit_suffix
syntax "f16"   : rise_expr_scilit_suffix
syntax "f32"   : rise_expr_scilit_suffix
syntax "f64"   : rise_expr_scilit_suffix

declare_syntax_cat                                            rise_expr
syntax num         (noWs rise_expr_numlit_suffix)?          : rise_expr
syntax scientific  (noWs rise_expr_scilit_suffix)?          : rise_expr
syntax ident                                                : rise_expr
syntax "fun" "(" ident+ (":" rise_type)? ")" "=>" rise_expr : rise_expr
syntax "fun"     ident+ (":" rise_type)?     "=>" rise_expr : rise_expr
syntax "fun" "(" ident+ (":" rise_kind)  ")" "=>" rise_expr : rise_expr
syntax "fun" "{" ident+ (":" rise_kind)  "}" "=>" rise_expr : rise_expr
syntax "fun"     ident+ ":" rise_kind        "=>" rise_expr : rise_expr
syntax "let" ident ":=" rise_expr "in" rise_expr : rise_expr
syntax:10 rise_expr:10 "+" rise_expr:11                     : rise_expr
syntax:20 rise_expr:20 "*" rise_expr:21                     : rise_expr
syntax rise_expr ".1" : rise_expr
syntax rise_expr ".2" : rise_expr


-- nat2nat
syntax:50 rise_expr:50 "(" ident "↦" rise_nat ")"           : rise_expr
syntax:50 rise_expr:50 "(" ident "↦" rise_data ")"          : rise_expr

syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:50 rise_expr:50 rise_nat                             : rise_expr
syntax:50 rise_expr:50 rise_data                            : rise_expr
syntax:40 rise_expr:40 "|>" rise_expr:41                    : rise_expr
syntax:40 rise_expr:40 "<|" rise_expr:41                    : rise_expr
syntax:41 rise_expr:41 ">>" rise_expr:42                    : rise_expr
syntax:41 rise_expr:41 "<<" rise_expr:42                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

macro_rules
  | `(rise_expr| let $x:ident := $v:rise_expr in $b:rise_expr) =>
    `(rise_expr| ((fun $x:ident => $b) $v:rise_expr))
  | `(rise_expr| fun $x:ident => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident) => $b:rise_expr)

  | `(rise_expr| fun $x:ident : $t:rise_type => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident : $t:rise_type) => $b:rise_expr )

  | `(rise_expr| fun $x:ident : $t:rise_kind => $b:rise_expr) =>
    `(rise_expr| fun ($x:ident : $t:rise_kind) => $b:rise_expr )

  | `(rise_expr| fun $x:ident $y:ident $xs:ident* => $e:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun $x => fun $y => $e)
    | _ =>
      `(rise_expr| fun $x => fun $y => fun $xs* => $e)

  | `(rise_expr| fun $x:ident $y:ident $xs:ident* : $k:rise_type => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => fun ($xs* : $k:rise_type) => $b:rise_expr)
  | `(rise_expr| fun ($x:ident $y:ident $xs:ident* : $k:rise_type) => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_type) => fun ($y : $k:rise_type) => fun ($xs* : $k:rise_type) => $b:rise_expr)
  | `(rise_expr| fun ($x:ident $y:ident $xs:ident* : $k:rise_kind) => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => fun ($xs* : $k:rise_kind) => $b:rise_expr)
  | `(rise_expr| fun {$x:ident $y:ident $xs:ident* : $k:rise_kind} => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => $b:rise_expr)
    | _ =>
      `(rise_expr| fun {$x : $k:rise_kind} => fun {$y : $k:rise_kind} => fun {$xs* : $k:rise_kind} => $b:rise_expr)
  | `(rise_expr| fun  $x:ident $y:ident $xs:ident* : $k:rise_kind  => $b:rise_expr) =>
    match xs with
    | #[] =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => $b:rise_expr)
    | _ =>
      `(rise_expr| fun ($x : $k:rise_kind) => fun ($y : $k:rise_kind) => fun ($xs* : $k:rise_kind) => $b:rise_expr)


  | `(rise_expr| $f:rise_expr >> $g:rise_expr) =>
    let x := mkIdent `x
    `(rise_expr| fun $x => $g ($f $x:ident))

  | `(rise_expr| $f:rise_expr << $g:rise_expr) =>
    `(rise_expr| $g >> $f)
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    `(rise_expr| $f:rise_expr $e:rise_expr)
  | `(rise_expr| $f:rise_expr <| $e:rise_expr) => do
    `(rise_expr| $f:rise_expr $e:rise_expr)
  | `(rise_expr| ($e:rise_expr)) => do
    `(rise_expr| $e)

set_option hygiene false in
macro_rules
  | `(rise_expr| $a:rise_expr + $b:rise_expr) =>
    `(rise_expr| (add $a:rise_expr $b:rise_expr))
  | `(rise_expr| $a:rise_expr * $b:rise_expr) =>
    `(rise_expr| (mul $a:rise_expr $b:rise_expr))
  | `(rise_expr| $x:rise_expr.1) =>
    `(rise_expr| (fst $x:rise_expr))
  | `(rise_expr| $x:rise_expr.2) =>
    `(rise_expr| (snd $x:rise_expr))

