module

public import SympyProofs.Calculus.Risch.Program.Normal

/-! The linear system over the rationals equivalent to a linear equation over the field of a
tower whose unknowns are constants: the terms are put over one denominator, and the
coefficients of each monomial in the generators give one equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

/-- Numerators of the terms over one common denominator. -/
def numerators : List (Term n) → List (MPoly n) × MPoly n
  | [] => ([], MPoly.scalar 1)
  | c :: cs =>
    (c.fraction.1.mul (numerators cs).2 :: (numerators cs).1.map fun w => w.mul c.fraction.2,
      c.fraction.2.mul (numerators cs).2)

/-- Every monomial occurring in some polynomial of the list. -/
def monomials (ws : List (MPoly n)) : List (Mono n) := ws.flatMap fun w => w.map (·.1)

/-- One row for each monomial: its coefficients in the numerators. -/
def rowsOf (as : List (Term n)) : List (List Rat) :=
  (monomials (numerators as).1).map fun μ => (numerators as).1.map (MPoly.coeff μ)

end SympyProofs.Calculus.Risch
