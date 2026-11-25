module

public import SympyProofs.Calculus.Risch.Program.Term

/-! Exact comparison of terms. A term is written as a quotient of two polynomials in the
generators with rational coefficients, treating the generators as independent variables,
and two terms are compared by cross multiplication. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- The exponents of a monomial in `n` generators. -/
abbrev Mono (n : Nat) := Vector Nat n

/-- A polynomial in `n` generators: monomials with coefficients. A monomial may occur more
than once, and its coefficient is then the sum. -/
abbrev MPoly (n : Nat) := List (Mono n × Rat)

namespace MPoly

variable {n : Nat}

def scalar (c : Rat) : MPoly n := if c == 0 then [] else [(Vector.replicate n 0, c)]

def indet (i : Fin n) : MPoly n := [(Vector.ofFn fun j => if i == j then 1 else 0, 1)]

def neg (p : MPoly n) : MPoly n := p.map fun t => (t.1, -t.2)

def mulTerm (m : Mono n) (a : Rat) (q : MPoly n) : MPoly n :=
  q.map fun t => (Vector.zipWith (· + ·) m t.1, a * t.2)

/-- Add one monomial, combining it with an equal one and dropping a vanishing sum. -/
def addTerm (m : Mono n) (a : Rat) : MPoly n → MPoly n
  | [] => if a == 0 then [] else [(m, a)]
  | (k, b) :: p =>
    if m == k then
      if a + b == 0 then p else (m, a + b) :: p
    else (k, b) :: addTerm m a p

def add : MPoly n → MPoly n → MPoly n
  | [], q => q
  | (m, a) :: p, q => addTerm m a (add p q)

def mul : MPoly n → MPoly n → MPoly n
  | [], _ => []
  | (m, a) :: p, q => add (mulTerm m a q) (mul p q)

/-- The coefficient of a monomial: the sum over all its occurrences. -/
def coeff (m : Mono n) : MPoly n → Rat
  | [] => 0
  | (k, a) :: p => (if k == m then a else 0) + coeff m p

def isZero (p : MPoly n) : Bool := p.all fun t => coeff t.1 p == 0

end MPoly

namespace Term

variable {n : Nat}

/-- A numerator and a denominator, without cancellation. -/
def fraction : Term n → MPoly n × MPoly n
  | .const c => (MPoly.scalar c, MPoly.scalar 1)
  | .gen i => (MPoly.indet i, MPoly.scalar 1)
  | .neg a => ((fraction a).1.neg, (fraction a).2)
  | .add a b =>
    (((fraction a).1.mul (fraction b).2).add ((fraction b).1.mul (fraction a).2),
      (fraction a).2.mul (fraction b).2)
  | .sub a b =>
    (((fraction a).1.mul (fraction b).2).add ((fraction b).1.mul (fraction a).2).neg,
      (fraction a).2.mul (fraction b).2)
  | .mul a b => ((fraction a).1.mul (fraction b).1, (fraction a).2.mul (fraction b).2)
  | .div a b => ((fraction a).1.mul (fraction b).2, (fraction a).2.mul (fraction b).1)

/-- Two terms denote the same element, where both are defined. -/
def equiv (a b : Term n) : Bool :=
  (((fraction a).1.mul (fraction b).2).add ((fraction b).1.mul (fraction a).2).neg).isZero

/-- The term denotes zero, where it is defined. -/
def isZero (a : Term n) : Bool := a.equiv (.const 0)

/-- No denominator in the term denotes zero. -/
def defined : Term n → Bool
  | .const _ | .gen _ => true
  | .neg a => a.defined
  | .add a b | .sub a b | .mul a b => a.defined && b.defined
  | .div a b => a.defined && b.defined && !b.isZero

/-- The rational number a term denotes, if it denotes one. -/
def scalar? (e : Term n) : Option Rat :=
  match (fraction e).2.find? fun t => MPoly.coeff t.1 (fraction e).2 != 0 with
  | none => none
  | some m =>
    let c := MPoly.coeff m.1 (fraction e).1 / MPoly.coeff m.1 (fraction e).2
    if e.equiv (.const c) then some c else none

end Term

end SympyProofs.Calculus.Risch
