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

mutual
structure Field where
  type : CType
  userName : Lean.Name
deriving Repr, BEq

inductive CType where
  | scalar (s : CScalar) (const : Bool := false)
  | pointer (valueType : CType) (const : Bool := false)
  | array (elemType : CType) (size : Option Nat) (const : Bool := false)
  | struct (userName : Lean.Name) (fields : List Field) (const : Bool := false)
  | union (fields : List CType) (const : Bool := false)
deriving Repr, BEq

end

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
  | forLoop (init : CDecl) (cond : CExpr) (increment : CExpr) (body : CStmt)
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
  --arithmetic expr
deriving Repr, BEq

end

inductive CNode where
  | decl (d : CDecl)
  | stmt (s : CStmt)
  | expr (e : CExpr)
deriving Repr, BEq

--- string representation

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

mutual
instance : ToString Field where
  toString s := s!"\n{toString s.userName} : {CType.toString s.type}"

def FieldList.ToString: List Field → String
  | [] => s!""
  | x :: ys => s!"    {x} {FieldList.ToString ys}"

def CType.toString : CType → String
  | CType.scalar s const                 => match const with
                                          | false => s!"const {s}"
                                          | true => s!"{s}"
  | CType.pointer valueType const        => match const with
                                          | false => s!"const {CType.toString valueType}"
                                          | true => s!"{CType.toString valueType}*"
  | CType.array elemType size const      => match size with
                                          | some  y => s!"{CType.toString elemType}[{y}]"
                                          | none => s!"{CType.toString elemType}"
  | CType.struct userName fields const   => s!"{userName} {FieldList.ToString fields}"
  | CType.union fields const             => s!" still needs to be done"

instance : ToString CType where
  toString := CType.toString

end


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
def CDeclList.ToString: List CDecl → String
  | [] => s!""
  | x :: ys => s!"    {x} {CDeclList.ToString ys}"

def CStmtList.ToString: List CStmt → String
  | [] => s!""
  | x :: ys => s!"    {x} {CStmtList.ToString ys}"

def CExprList.ToString: List CExpr → String
  | [] => s!""
  | x :: ys => s!"    {x} { CExprList.ToString ys}"

instance : ToString CDecl where
  toString
    | .fn userName rv param body => s!"{rv} {userName.toString}({CDeclList.ToString param}) \n {body}"
    | .var userName t init => match init with
                                | some y => s!"{t} {userName} = {y}"
                                | none => s!"{t} {userName}"
    | .param userName t => s!"{userName}"
    | .label userName => s!"{userName}:"
    | .typeDef userName t => s!""
    | .structType userName fields => s!""


instance : ToString CStmt where
  toString
    | .block body => s!"{CStmtList.ToString body}"
    | .forLoop init cond increment body => s!""
    | .whileLoop cond body => s!""
    | .ifThenElse cond trueBody falseBody => s!""
    | .goTo label => s!""
    | .breakStmt => s!""
    | .continueStmt => s!""
    | .returnStmt x => s!""
    | .declStmt decl => s!""
    | .comment string => s!""
    | .code string => s!""
    | .exprStmt expr => s!""

instance : ToString CExpr where
  toString
    | .assignment lvalue rvalue => s!""
    | .declRef userName => s!""
    | .funCall fn args => s!""
    | .arraySubscript array index => s!""
    | .structMemberAccess struct member => s!""
    | .unaryExpr op expr => s!""
    | .binaryExpr op lhs rhs => s!""
    | .ternaryExpr cond thenE elseE => s!""
    | .cast type expr => s!""
    | .literal code => s!""
    | .arrayLiteral t inits => s!""
    | .recordLiteral t fst snd => s!""
end

instance : ToString CNode where
  toString
    | .decl d => s!"{d}"
    | .stmt s => s!"{s}"
    | .expr e => s!"{e}"
