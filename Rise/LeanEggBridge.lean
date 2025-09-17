import Lean

private opaque EGraph.Pointed : NonemptyType.{0}

def EGraph := EGraph.Pointed.type

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure EggResult where
  success : Bool
  info    : String
  egraph? : Option EGraph
deriving Inhabited

@[extern "run_egg_c"]
opaque runEgg (flag : Bool) (input : Array String) : Lean.MetaM EggResult

@[extern "query_egraph"]
opaque EGraph.query (query : String) : EggResult
