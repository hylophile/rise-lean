import Lean

abbrev RewriteResult P := Except String P

abbrev Strategy P := P -> RewriteResult P

def Strategy.id : Strategy P := fun x => Except.ok x
def Strategy.fail : Strategy P := fun _ => Except.error "fail"

def Strategy.seq (fs ss : Strategy P) : Strategy P :=
    fun p => match fs p with
        | .ok p => ss p
        | e => e

def Strategy.leftChoice (fs ss : Strategy P) : Strategy P :=
    fun p => match fs p with
        | .error _ => ss p
        | p => p

def Strategy.try (s : Strategy P) : Strategy P :=
    s.leftChoice .id

partial
def Strategy.repeat (s : Strategy P) : Strategy P :=
    .try (s.seq (.repeat s) )

def Strategy.repeatNTimes (n: Nat) (s: Strategy P) : Strategy P :=
    match n with
        | .zero => .id
        | .succ n => s.seq (repeatNTimes n s)

class Traversable (P : Type) where
    all   : Strategy P -> Strategy P
    one   : Strategy P -> Strategy P
    some  : Strategy P -> Strategy P

partial
def Strategy.topDown [Traversable P] (s : Strategy P): Strategy P :=
    s.leftChoice (Traversable.one (.topDown s))

partial
def Strategy.bottomUp [Traversable P] (s : Strategy P): Strategy P :=
    (Traversable.one (.bottomUp s)).leftChoice s

def Strategy.normalize [Traversable P] (s: Strategy P) : Strategy P :=
    .repeat (.topDown s)
