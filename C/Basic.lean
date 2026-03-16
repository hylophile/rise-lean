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
partial def Field.toString (f : Field) : String :=
  s!"\n{toString f.userName} : {CType.toString f.type}"

partial def FieldList.ToString: List Field → String
   | [] => s!""
   | x :: ys => s!"{Field.toString x}; \n{FieldList.ToString ys}"

partial def CTypeList.ToString: List CType → String
   | [] => s!""
   | x :: ys => s!"{CType.toString x}; \n{CTypeList.ToString ys}"

partial def CType.toString : CType → String
  | CType.scalar s const                 => match const with
                                          | false => s!"const {s}"
                                          | true => s!"{s}"
  | CType.pointer valueType const        => match const with
                                          | false => s!"const {CType.toString valueType}*"
                                          | true => s!"{CType.toString valueType}*"
  | CType.array elemType size const      => match size with
                                          | some  y => if const then s!"const {CType.toString elemType}[{y}]"
                                                        else s!"{CType.toString elemType}[{y}]"
                                          | none => if const then s!"const {CType.toString elemType}"
                                                    else s!"{CType.toString elemType}"
  | CType.struct userName fields const   => if const then "const struct " ++ toString userName ++ "{" ++FieldList.ToString fields ++ "}"
                                            else "const struct" ++ toString userName ++ "{" ++ FieldList.ToString fields ++ "}"
  | CType.union fields const             => if const then "const union " ++ CTypeList.ToString fields
                                            else "union " ++ CTypeList.ToString fields

end
instance : ToString Field where
  toString := Field.toString

instance : ToString CType where
  toString := CType.toString

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
  | x :: ys => s!"    {CDecl.toString x}, \n{CDeclList.ToString ys}"

def CStmtList.ToString: List CStmt → String
  | [] => s!""
  | x :: ys => s!"    {CStmt.toString x}; \n{CStmtList.ToString ys}"

def CExprList.ToString: List CExpr → String
  | [] => s!""
  | x :: ys => s!"    {CExpr.toString x}, \n{ CExprList.ToString ys}"

def CDecl.toString : CDecl → String
    | .fn userName rv param body => s!"{rv} {userName.toString}({CDeclList.ToString param}) \n {CStmt.toString body}"
    | .var userName t init => match init with
                                | some y => s!"{t} {userName} = {CExpr.toString y}"
                                | none => s!"{t} {userName}"
    | .param userName t => s!"{userName} {t}"
    | .label userName => s!"{userName}:"
    | .typeDef userName t => s!"typedef {t} {userName}"
    | .structType userName fields => s!"struct {userName} " ++ "{" ++ CDeclList.ToString fields ++ "}"


def CStmt.toString : CStmt → String
    | .block body => s!"{CStmtList.ToString body}"
    | .forLoop init cond increment body => "for (" ++ CDecl.toString init ++ ", " ++ CExpr.toString cond ++ "," ++ CExpr.toString increment ++ "){\n" ++  CStmt.toString body ++ "\n}"
    | .whileLoop cond body => "while(" ++ CExpr.toString cond ++ "){" ++ CStmt.toString body ++ "\n}"
    | .ifThenElse cond trueBody falseBody =>  let ifPart := "if (" ++ CExpr.toString cond ++ "){\n" ++  CStmt.toString trueBody ++ "}"
                                              match falseBody with
                                                | some y => ifPart ++ " else {" ++  CStmt.toString y ++ "}\n"
                                                | none => ifPart
    | .goTo label => s!"goto {label}"
    | .breakStmt => s!"break"
    | .continueStmt => s!"continue"
    | .returnStmt x => match x with
                        | some y => s!"return {CExpr.toString y}"
                        | none => "return"
    | .declStmt decl => CDecl.toString decl
    | .comment string => s!"// {string}"
    | .code string => string -- what does this represent?
    | .exprStmt expr => CExpr.toString expr

def CExpr.toString : CExpr → String
    | .assignment lvalue rvalue => s!"{CExpr.toString lvalue} = {CExpr.toString rvalue}"
    | .declRef userName => s!"{userName}"
    | .funCall fn args => CExpr.toString fn ++ "(" ++ CStmtList.ToString args ++ ")"
    | .arraySubscript array index => CExpr.toString array ++ "[" ++ CExpr.toString index ++ "]"
    | .structMemberAccess struct member => CExpr.toString struct ++ "." ++ CExpr.toString member
    | .unaryExpr op expr => s!"{op}" ++ CExpr.toString expr
    | .binaryExpr op lhs rhs => s!"{CExpr.toString lhs} {op} {CExpr.toString rhs}"
    | .ternaryExpr cond thenE elseE => CExpr.toString cond ++ " ? " ++ CExpr.toString thenE ++ " : " ++ CExpr.toString elseE
    | .cast type expr => s!"({type}){CExpr.toString expr}"
    | .literal code => s!"{code}"
    | .arrayLiteral t inits => "(" ++ toString t ++ "){" ++  CExprList.ToString inits ++"}"
    | .recordLiteral t fst snd => "(" ++ toString t ++ "){" ++ CExpr.toString fst ++ ", " ++ CExpr.toString snd ++ "}"
end

instance : ToString CDecl where
  toString := CDecl.toString

instance : ToString CStmt where
  toString := CStmt.toString

instance : ToString CExpr where
  toString := CExpr.toString

instance : ToString CNode where
  toString
    | .decl d => s!"{d}"
    | .stmt s => s!"{s}"
    | .expr e => s!"{e}"
