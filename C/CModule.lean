import C.Basic

-------------- Module Structure ----------------

-- includes
inductive IncludeDirective where
    | includeHeader (name : String)
    | includeSource (path : String)

instance : ToString IncludeDirective where
  toString
    | .includeHeader n => s!"#include <{n}>"
    | .includeSource path => s!"#include \"{path}\""

-- functions
structure Function where
    code : CDecl

def Function.name (f : Function) : String :=
    match f.code with
        | .fn name .. => name.toString
        | _ => panic! s!"code should be a function declaration"

def Function.params (f : Function) : List CDecl :=
    match f.code with
        | .fn _ _ params .. => params
        | _ => panic! s!"code should be a function declaration"

def Function.returnType (f : Function) : CType :=
    match f.code with
        | .fn _ rt .. => rt
        | _ => panic! s!"code should be a function declaration"

-- outputs C functions
def Function.ToFormat (f : Function) : Std.Format :=
    CDecl.ToFormat f.code

-------------- C Module ----------------

structure Module where
    includes : List IncludeDirective
    decls : List CDecl
    functions : List Function

def includesList (incl : List IncludeDirective) : Std.Format :=
    match incl with
        | [] => Std.Format.line
        | x :: ys => toString x ++ Std.Format.line ++ includesList ys

def functionsList (incl : List Function) : Std.Format :=
    match incl with
        | [] => ""
        | x :: ys => Function.ToFormat x ++ Std.Format.line ++ functionsList ys

-- outputs a hole functional C programm
def Module.ToFormat (m : Module) : Std.Format :=
    includesList m.includes ++ CDeclList.ToFormat m.decls ++ functionsList m.functions

instance : ToString Module where
  toString e := Std.Format.pretty (Module.ToFormat e)

def compose (m1 m2 : Module) : Module :=
    let cIncludes := m1.includes.append m2.includes
    let cDecls := m1.decls.append m2.decls
    let cFunctions := m1.functions.append m2.functions
    {includes := cIncludes, decls := cDecls, functions := cFunctions}
