import Lean
import Rise.Elab.RElabM

open Lean Parser Elab Command Meta

declare_syntax_cat egg_op
syntax "+" : egg_op
syntax "-" : egg_op
syntax "*" : egg_op
syntax "/" : egg_op
syntax "^" : egg_op
syntax "term_mvar" : egg_op
syntax "term_bvar" : egg_op
syntax "type_mvar" : egg_op
syntax "type_bvar" : egg_op
syntax "array" : egg_op
syntax "vector" : egg_op
syntax "pair" : egg_op
syntax "index" : egg_op

declare_syntax_cat egg_expr
syntax num : egg_expr
syntax "-" num : egg_expr
syntax ident : egg_expr
syntax "bool" : egg_expr
syntax "int" : egg_expr
syntax "i8" : egg_expr
syntax "i16" : egg_expr
syntax "i32" : egg_expr
syntax "i64" : egg_expr
syntax "u8" : egg_expr
syntax "u16" : egg_expr
syntax "u32" : egg_expr
syntax "u64" : egg_expr
syntax "f16" : egg_expr
syntax "f32" : egg_expr
syntax "f64" : egg_expr
syntax "natType" : egg_expr
syntax "(" egg_op egg_expr ")" : egg_expr
syntax "(" egg_op egg_expr egg_expr ")" : egg_expr

declare_syntax_cat egg_pair
syntax egg_expr "=" egg_expr : egg_pair

declare_syntax_cat egg_map
syntax (egg_pair,*) : egg_map


private def elabName (x:Syntax) : RElabM (Name × Nat) :=
  match x.getId.toString.split (· == '_') with
    | [name,id] => match id.toNat? with
      | some id => pure (name.toName, id)
      | none => throwUnsupportedSyntax
    | e => throwError m!"{e}"


private partial def elabEggExpr : Syntax → RElabM SubstEnum
  | `(egg_expr| bool) => return .data <| RData.scalar .bool
  | `(egg_expr|  int) => return .data <| RData.scalar .int
  | `(egg_expr|   i8) => return .data <| RData.scalar .i8
  | `(egg_expr|  i16) => return .data <| RData.scalar .i16
  | `(egg_expr|  i32) => return .data <| RData.scalar .i32
  | `(egg_expr|  i64) => return .data <| RData.scalar .i64
  | `(egg_expr|   u8) => return .data <| RData.scalar .u8
  | `(egg_expr|  u16) => return .data <| RData.scalar .u16
  | `(egg_expr|  u32) => return .data <| RData.scalar .u32
  | `(egg_expr|  u64) => return .data <| RData.scalar .u64
  | `(egg_expr|  f16) => return .data <| RData.scalar .f16
  | `(egg_expr|  f32) => return .data <| RData.scalar .f32
  | `(egg_expr|  f64) => return .data <| RData.scalar .f64
  | `(egg_expr|  natType) => return .data <| RData.natType
  | `(egg_expr| $n:num) => do
    let n := n.getNat
    return .nat <| RNat.nat n
  | `(egg_expr| -$n:num) => do
    let n := n.getNat
    return .nat <| RNat.minus (RNat.nat 0) (RNat.nat n)
  | `(egg_expr| (term_mvar $x:ident)) => do
    let (n,id) ← elabName x
    return .nat <| RNat.mvar id n
  | `(egg_expr| (term_bvar $x:ident)) => do
    let (n,id) ← elabName x
    return .nat <| RNat.bvar id n
  | `(egg_expr| (type_mvar $x:ident)) => do
    let (n,id) ← elabName x
    return .data <| RData.mvar id n
  | `(egg_expr| (type_bvar $x:ident)) => do
    let (n,id) ← elabName x
    return .data <| RData.bvar id n
  | `(egg_expr| (+ $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .nat <| RNat.plus e1 e2
  | `(egg_expr| (- $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .nat <| RNat.minus e1 e2
  | `(egg_expr| (* $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .nat <| RNat.mult e1 e2
  | `(egg_expr| (/ $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .nat <| RNat.div e1 e2
  | `(egg_expr| (^ $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .nat <| RNat.pow e1 e2
  | `(egg_expr| (array $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat _ => throwError "type error"
      | .data x => pure x
    return .data <| RData.array e1 e2
  | `(egg_expr| (vector $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    let e2 ← match (← elabEggExpr e2) with
      | .nat _ => throwError "type error"
      | .data x => pure x
    return .data <| RData.vector e1 e2
  | `(egg_expr| (pair $e1:egg_expr $e2:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat _ => throwError "type error"
      | .data x => pure x
    let e2 ← match (← elabEggExpr e2) with
      | .nat _ => throwError "type error"
      | .data x => pure x
    return .data <| RData.pair e1 e2
  | `(egg_expr| (index $e1:egg_expr)) => do
    let e1 ← match (← elabEggExpr e1) with
      | .nat x => pure x
      | .data _ => throwError "type error"
    return .data <| RData.index e1
  | e => throwError e

private def elabEggPair : Syntax → RElabM (Nat × SubstEnum)
  | `(egg_pair| $s:egg_expr = $e:egg_expr) => do
    let id ← match (← elabEggExpr s) with
      | .nat (.mvar id _) => pure id
      | .data (.mvar id _) => pure id
      | _ => throwUnsupportedSyntax
    let e ← elabEggExpr e
    return (id,e)
  | _ => throwUnsupportedSyntax

private def elabEggMap : Syntax → RElabM Substitution
  | `(egg_map| $p:egg_pair,*) => do
    let ps ← p.getElems.raw.mapM (fun x => elabEggPair x)
    return ps.toList
  | _ => throwUnsupportedSyntax



private def parseEggMap (s : String) : TermElabM (Except String Syntax) := do
  let env ← getEnv
  let stxExcept := Parser.runParserCategory env `egg_map s
  match stxExcept with
  | .ok stx => return .ok stx
  | .error err => return .error s!"egg parse error: {err}\ninput: '{s}'"



def elabEggSolveOutput (s : String) : RElabM (Except String Substitution) := do
    if s == "" then return .ok []
    let stx ← parseEggMap s
    match stx with
    | .ok stx =>
      let stx ← liftMacroM <| expandMacros stx
      let subst ← elabEggMap stx
      return .ok subst
    | .error err => return .error err


 -- #eval liftToTermElabM <| elabEggSolveOutput "(type_mvar s_4)=(pair f32 f32),(type_mvar s_8)=f32,(type_mvar t_5)=f32,(term_mvar n_0)=(term_bvar n_0),(type_mvar d_6)=f32,(type_mvar t_9)=f32,(term_mvar n_7)=(term_bvar n_0),(type_mvar t_1)=f32,(type_mvar t_2)=f32,(term_mvar n_3)=(term_bvar n_0)"

 -- #eval liftToTermElabM <| elabEggSolveOutput "(type_mvar d_6)=f32,(type_mvar s_8)=f32,(type_mvar t_2)=f32,(term_mvar n_7)=(term_bvar n_0),(type_mvar t_9)=f32,(type_mvar t_1)=f32,(type_mvar s_4)=(pair f32 f32),(type_mvar t_5)=f32,(term_mvar n_0)=(term_bvar n_0),(term_mvar n_3)=(term_bvar n_0)"

 -- #eval liftToTermElabM <| elabEggSolveOutput "(type_mvar s_8)=f32,(type_mvar t_2)=f32,(type_mvar t_5)=f32,(type_mvar t_1)=f32,(term_mvar n_7)=(term_bvar n_0),(term_mvar n_3)=(term_bvar n_0),(type_mvar t_9)=f32,(term_mvar n_0)=(term_bvar n_0),(type_mvar s_4)=(pair f32 f32),(type_mvar d_6)=f32"

-- #eval liftToTermElabM <| elabEggSolveOutput "(type_mvar s_35)=(array (+ 1 (/ (- (+ (+ 3 (/ (term_bvar w_0) 2)) 1) 2) 1)) (array 2 (array 2 f32))),(type_mvar t_53)=(array 2 f32),(term_mvar n_24)=2,(type_mvar t_29)=f32,(type_mvar t_26)=(array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) f32),(type_mvar t_42)=(array 2 f32),(type_mvar t_54)=(index 2),(type_mvar t_8)=f32,(term_mvar n_60)=(+ (+ (/ (term_bvar h_1) 2) 3) 1),(term_mvar m_13)=(+ (term_mvar n_1) (- (+ 2 (* 2 (/ (term_bvar h_1) 2))) (term_bvar h_1))),(type_mvar s_50)=(array 2 f32),(type_mvar anonymous_12)=(array (+ (/ (term_bvar h_1) 2) 3) (array (+ 3 (/ (term_bvar w_0) 2)) f32)),(type_mvar d_11)=(array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) f32),(term_mvar n_37)=(+ 1 (/ (- (+ (+ 3 (/ (term_bvar w_0) 2)) 1) 2) 1)),(type_mvar t_36)=(array (+ 1 (/ (- (+ (+ 3 (/ (term_bvar w_0) 2)) 1) 2) 1)) (array 2 (array 2 f32))),(term_mvar m_7)=(+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0))),(type_mvar anonymous_47)=(array 2 (array 2 f32)),(type_mvar d_62)=f32,(term_mvar n_48)=2,(type_mvar t_39)=(array 2 (array 2 f32)),(term_mvar n_52)=2,(type_mvar t_55)=(array 2 f32),(type_mvar anonymous_0)=(array (+ (/ (term_bvar h_1) 2) 3) (array(+ 3 (/ (term_bvar w_0) 2)) f32)),(type_mvar d_67)=f32,(term_mvar n_27)=(+ 1 (/ (- (+ (+ 3 (/ (term_bvar w_0) 2)) 1) 2) 1)),(type_mvar t_14)=(array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) f32),(term_mvar n_20)=(+ 1 (/ (- (+ (+ (/ (term_bvar h_1) 2) 3) 1) 2) 1)),(term_mvar m_17)=2,(type_mvar s_2)=(array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) f32),(type_mvar t_32)=(array 2 f32),(type_mvar t_22)=(array 2 (array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) f32)),(term_mvar m_31)=2"
