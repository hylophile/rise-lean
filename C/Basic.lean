import DPIA.Basic

-- copied from Nates RISE representation
inductive CScalar
  | void
  | char  -- how to handle const char?
  | uchar
  | int
  | i8
  | i16
  | i32
  | i64
  | u8
  | u16
  | u32
  | u64
  | float
  | usize
  | isize
  | double
deriving Repr, BEq

inductive CNat
  | declRef (ref : Lean.Name)
  | nat  (n : Nat)
  | plus (n : CNat) (m : CNat)
  | minus (n : CNat) (m : CNat)
  | mult (n : CNat) (m : CNat)
  | div (n : CNat) (m : CNat)
  | pow (n : CNat) (m : CNat)
deriving Repr, BEq

inductive CUnaryOp where
  | ex
  | minus
  | point
  | addr
deriving Repr, BEq

inductive CBinaryOp where
  | plus
  | minus
  | mult
  | div
  | less
  | greater
  | lessThan
  | greaterThan
  | notEqual
  | equal
  | and
  | or
  | pow
  | mod
  | shift
deriving Repr, BEq

mutual
structure Field where
  type : CType
  userName : Lean.Name
deriving Repr, BEq

inductive CType where
  | scalar (s : CScalar) (const : Bool := false)
  | pointer (valueType : CType) (const : Bool := false)
  | array (elemType : CType) (size : Option CNat) (const : Bool := false) -- should be RNat or own nat
  | struct (userName : Lean.Name) (fields : List Field) (const : Bool := false)
  | union (fields : List CType) (const : Bool := false)
deriving Repr, BEq

end

mutual
inductive CDecl where
  | fn (userName : Lean.Name) (rv : CType) (param : List CDecl) (body : CStmt)
  | var (userName : Lean.Name) (t : CType) (init : Option CExpr)
  | param (userName : Lean.Name) (t : CType)
  | label (userName : Lean.Name)
  | typeDef (userName : Lean.Name) (t : CType)
  | structType (userName : Lean.Name) (fields : List CDecl)
deriving Repr, BEq

inductive CStmt where
  | block (body : List CStmt)
  | stmts (fst : CStmt) (snd : CStmt)
  | forLoop (init : CStmt) (cond : CExpr) (increment : CExpr) (body : CStmt)
  | whileLoop (cond : CExpr) (body : CStmt)
  | ifThenElse (cond : CExpr) (trueBody : CStmt) (falseBody : Option CStmt)
  | goTo (label : Lean.Name)
  | breakStmt
  | continueStmt
  | returnStmt (x : Option CExpr)
  | declStmt (decl : CDecl)
  | comment (string : String)
  | code (string : String)
  | exprStmt (expr : CExpr)
deriving Repr, BEq

inductive CExpr
  | assignment (lvalue : CExpr) (rvalue : CExpr)
  | declRef (userName : Lean.Name)
  | funCall (fn : CExpr) (args : List CStmt)
  | arraySubscript (array : CExpr) (index : CExpr)
  | structMemberAccess (struct : CExpr) (member : CExpr)
  | unaryExpr (op : CUnaryOp) (expr : CExpr)
  | binaryExpr (op : CBinaryOp) (lhs : CExpr) (rhs : CExpr)
  | ternaryExpr (cond : CExpr) (thenE : CExpr) (elseE : CExpr)
  | cast (type : CType) (expr : CExpr)
  | literal (code : String)
  | arrayLiteral (t : CType) (inits : List CExpr)
  | recordLiteral (t : CType) (fst : CExpr) (snd : CExpr)
  | arithmeticExpr (n : CNat) --- needs fixing
deriving Repr, BEq

end

inductive CNode where
  | decl (d : CDecl)
  | stmt (s : CStmt)
  | expr (e : CExpr)
deriving Repr, BEq

---------------- string representations -----------------

-- modified from Nate
instance : ToString CScalar where
  toString
    | .void => "void"
    | .char => "char"
    | .uchar => "uchar"
    | .int  => "int"
    | .i8   => "i8"
    | .i16  => "i16"
    | .i32  => "i32"
    | .i64  => "i64"
    | .u8   => "u8"
    | .u16  => "u16"
    | .u32  => "u32"
    | .u64  => "u64"
    | .float => "float"
    | .usize => "usize"
    | .isize => "isize"
    | .double => "double"

instance : ToString CNat where
  toString :=
    let rec go : CNat → String
      | .declRef ref => s!"{ref}"
      | .nat n => s!"{n}"
      | .plus n m => s!"({go n}+{go m})"
      | .minus n m => s!"({go n}-{go m})"
      | .mult n m => s!"({go n}*{go m})"
      | .div n m => s!"({go n}/{go m})"
      | .pow n m => s!"({go n}^{go m})"
    go

def setNest (indent : Int) (f : Std.Format) : Std.Format :=
  Std.Format.nest indent f

mutual
partial def Field.ToFormat (f : Field) : Std.Format :=
  s!"{toString f.userName} : {CType.ToFormat f.type}"

partial def FieldList.ToFormat: List Field → Std.Format
   | [] => s!""
   | x :: ys => Field.ToFormat x ++ ";" ++ Std.Format.line ++ FieldList.ToFormat ys

partial def CTypeList.ToFormat: List CType → Std.Format
   | [] => s!""
   | x :: ys => CType.ToFormat x ++ ";" ++ Std.Format.line ++ CTypeList.ToFormat ys

partial def CType.ToFormat : CType → Std.Format
  | CType.scalar s const                 => match const with
                                          | true => s!"const {s}"
                                          | false => s!"{s}"
  | CType.pointer valueType const        => match const with
                                          | true => s!"const {CType.ToFormat valueType}*"
                                          | false => s!"{CType.ToFormat valueType}*"
  | CType.array elemType size const      => match (size, const) with
                                          | (some  y, true) => s!"const {CType.ToFormat elemType}[{y}]"
                                          | (some y, false) => s!"{CType.ToFormat elemType}[{y}]"
                                          | (none, true) => s!"const {CType.ToFormat elemType}"
                                          | (none, false) => s!"{CType.ToFormat elemType}"
  | CType.struct userName fields const   => match const with
                                              | true => "const struct " ++ toString userName ++ "{" ++FieldList.ToFormat fields ++ "}"
                                              | false => "const struct" ++ toString userName ++ "{" ++ FieldList.ToFormat fields ++ "}"
  | CType.union fields const             => match const with
                                              | true => "const union " ++ CTypeList.ToFormat fields
                                              | false => "union " ++ CTypeList.ToFormat fields

end

instance : ToString Field where
  toString e := Std.Format.pretty (Field.ToFormat e)

instance : ToString CType where
  toString e := Std.Format.pretty (CType.ToFormat e)

instance : ToString CUnaryOp where
  toString
    | .ex => "!"
    | .minus => "-"
    | .point => "*"
    | .addr  => "&"

instance : ToString CBinaryOp where
  toString
    | .plus => "+"
    | .minus => "-"
    | .mult => "*"
    | .div => "/"
    | .less => "<"
    | .greater => ">"
    | .lessThan => "<="
    | .greaterThan => ">="
    | .notEqual => "!="
    | .equal => "=="
    | .and => "&&"
    | .or => "||"
    | .pow => "^"
    | .mod => "%"
    | .shift => ">>"

mutual
def CDeclList.ToFormat: List CDecl →  Std.Format
  | [] => s!""
  | x :: ys => CDecl.ToFormat x ++ ";" ++ Std.Format.line ++ CDeclList.ToFormat ys

def printFunParams : List CDecl →  Std.Format
  | [] => s!""
  | x :: [] => CDecl.ToFormat x
  | x :: ys => CDecl.ToFormat x ++ ", " ++ printFunParams ys

def printFunArgs : List CStmt →  Std.Format
  | [] => s!""
  | x :: [] => CStmt.ToFormat x
  | x :: ys => CStmt.ToFormat x ++ ", " ++ printFunArgs ys

def CStmtList.ToFormat: List CStmt → Std.Format
  | [] => s!""
  | x :: [] => CStmt.ToFormat x
  | x :: ys => CStmt.ToFormat x ++ Std.Format.line ++ CStmtList.ToFormat ys

def CExprList.ToFormat: List CExpr → Std.Format
  | [] => s!""
  | x :: ys => CExpr.ToFormat x ++ Std.Format.line ++ CExprList.ToFormat ys

def CDecl.ToFormat : CDecl → Std.Format
    | .fn userName rv param body => s!"{rv} {userName.toString}(" ++ printFunParams param ++ "){" ++ setNestAndLine 2 (CStmt.ToFormat body) ++ Std.Format.line ++ "}"
    | .var userName t init => match init with
                                | some y => s!"{t} {userName} = {CExpr.ToFormat y}"
                                | none => s!"{t} {userName}"
    | .param userName t => s!"{t} {userName}"
    | .label userName => s!"{userName}: ;"
    | .typeDef userName t => s!"typedef {t} {userName};"
    | .structType userName fields => s!"struct {userName} " ++ "{" ++ setNestAndLine 2 (CDeclList.ToFormat fields) ++ Std.Format.line ++ "};"


def CStmt.ToFormat : CStmt → Std.Format
    | .block body => "{" ++ (setNestAndLine 2 (CStmtList.ToFormat body)) ++  Std.Format.line ++ "}" ++ Std.Format.line
    | .stmts fst snd=> CStmt.ToFormat fst ++ Std.Format.line ++ CStmt.ToFormat snd
    | .forLoop init cond increment body => "for (" ++ CStmt.ToFormat init ++ " " ++ CExpr.ToFormat cond ++ "; " ++ CExpr.ToFormat increment ++ ")"
                                            ++ CStmt.ToFormat body
    | .whileLoop cond body => "while(" ++ CExpr.ToFormat cond ++ "){"
                                ++ setNestAndLine 2 (CStmt.ToFormat body)
                                ++ Std.Format.line ++"}"
    | .ifThenElse cond trueBody falseBody =>  let ifPart := "if (" ++ CExpr.ToFormat cond ++ "){" ++ setNestAndLine 2 (CStmt.ToFormat trueBody) ++ Std.Format.line ++ "}"
                                              match falseBody with
                                                | some y => ifPart ++ " else {" ++  setNestAndLine 2 (CStmt.ToFormat y) ++ Std.Format.line ++ "}"
                                                | none => ifPart
    | .goTo label => s!"goto {label};"
    | .breakStmt => s!"break;"
    | .continueStmt => s!"continue;"
    | .returnStmt x => match x with
                        | some y => s!"return {CExpr.ToFormat y};"
                        | none => "return;"
    | .declStmt decl => CDecl.ToFormat decl ++ ";"
    | .comment string => s!"/* {string} */"
    | .code string => string -- what does this represent?
    | .exprStmt expr => CExpr.ToFormat expr ++ ";"

def CExpr.ToFormat : CExpr → Std.Format
    | .assignment lvalue rvalue => s!"{CExpr.ToFormat lvalue} = {CExpr.ToFormat rvalue}"
    | .declRef userName => s!"{userName}"
    | .funCall fn args => CExpr.ToFormat fn ++ "(" ++ printFunArgs args ++ ")"
    | .arraySubscript array index => CExpr.ToFormat array ++ "[" ++ CExpr.ToFormat index ++ "]"
    | .structMemberAccess struct member => CExpr.ToFormat struct ++ "." ++ CExpr.ToFormat member
    | .unaryExpr op expr => toString op ++ CExpr.ToFormat expr
    | .binaryExpr op lhs rhs => Std.Format.paren s!"{CExpr.ToFormat lhs} {op} {CExpr.ToFormat rhs}"
    | .ternaryExpr cond thenE elseE => CExpr.ToFormat cond ++ " ? " ++ CExpr.ToFormat thenE ++ " : " ++ CExpr.ToFormat elseE
    | .cast type expr => s!"({type}){CExpr.ToFormat expr}"
    | .literal code => s!"{code}"
    | .arrayLiteral t inits => "(" ++ toString t ++ "){" ++  CExprList.ToFormat inits ++"}"
    | .recordLiteral t fst snd => "(" ++ toString t ++ "){" ++ CExpr.ToFormat fst ++ ", " ++ CExpr.ToFormat snd ++ "}"
    | .arithmeticExpr n => s!"{n}"
end

instance : ToString CDecl where
  toString e := Std.Format.pretty (CDecl.ToFormat e)

instance : ToString CStmt where
  toString e := Std.Format.pretty (CStmt.ToFormat e)

instance : ToString CExpr where
  toString e := Std.Format.pretty (CExpr.ToFormat e)

instance : ToString CNode where
  toString
    | .decl d => s!"{d}"
    | .stmt s => s!"{s}"
    | .expr e => s!"{e}"



-------------------  inhabited instances ---------------

instance : Inhabited CType :=
  ⟨CType.scalar (.int)⟩

instance : Inhabited CDecl :=
  ⟨CDecl.label (Lean.Name.mkSimple "failed")⟩

instance : Inhabited CStmt :=
  ⟨CStmt.breakStmt⟩

instance : Inhabited CExpr :=
  ⟨CExpr.literal "failed"⟩

instance : Inhabited CNat :=
  ⟨CNat.nat 0⟩

--------------- additional functions -------------

def CNatToRNat : CNat → RNat
  | .declRef ref => .bvar 0 ref
  | .plus n m => .plus (CNatToRNat n) (CNatToRNat m)
  | .minus n m => .minus (CNatToRNat n) (CNatToRNat m)
  | .mult n m => .mult (CNatToRNat n) (CNatToRNat m)
  | .div n m => .div (CNatToRNat n) (CNatToRNat m)
  | .pow n m => .pow (CNatToRNat n) (CNatToRNat m)
  | .nat n => .nat n

def RNatToCNatSimplified : RNat → CNat
  | .bvar _ name => .declRef name
  | .plus n m => let nC := RNatToCNatSimplified n
                 let mC := RNatToCNatSimplified m
                 match (nC, mC) with
                  | (.nat x, .nat y) => .nat (x+y)
                  | (.nat x, _) => if x == 0 then mC
                                 else .plus nC mC
                  |  (_ , .nat y) => if y == 0 then nC
                                   else .plus nC mC
                  | (_, _) => .plus nC mC
  | .minus n m=> let nC := RNatToCNatSimplified n
                 let mC := RNatToCNatSimplified m
                 match (nC, mC) with
                  | (.nat x, .nat y) => if x+y < 0 then .minus nC mC
                                        else .nat (x+y)
                  |  (_ , .nat y) => if y == 0 then nC
                                   else .minus nC mC
                  | (_, _) => .plus nC mC
  | .mult n m=> let nC := RNatToCNatSimplified n
                let mC := RNatToCNatSimplified m
                match (nC, mC) with
                  | (.nat x, .nat y) => .nat (x*y)
                  | (.nat x, _) => if x == 1 then mC
                                 else .mult nC mC
                  |  (_ , .nat y) => if y == 1 then nC
                                     else .mult nC mC
                  | (_, _) => .plus nC mC
  | .div n m=>  let nC := RNatToCNatSimplified n
                let mC := RNatToCNatSimplified m
                match (nC, mC) with
                  |  (_ , .nat y) => if y == 1 then nC
                                   else .div nC mC
                  | (_, _) => .plus nC mC
  | .pow n m=> .pow (RNatToCNatSimplified n) (RNatToCNatSimplified m)
  | .nat n => .nat n
  | _ => panic! s!"there should not be any mvars any more"
