module

public import SympyProofs.Calculus.Antiderivative.Algebra.NatBound
public import Mathlib.Algebra.Field.Rat

/-! The two bounds on natural numbers for the rational numbers: the instance `NatBound ℚ`.
Both are computed. `natBound` returns the natural number itself, and `natRootBound` is
Cauchy's estimate for the roots of a polynomial: a root is at most one plus the sum of the
absolute values of the lower coefficients divided by the absolute value of the leading one.

The proof that these estimates bound every natural root is in `Proof/Rat.lean`. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Rational

/-- The absolute value of a rational number. -/
def absQ (q : Rat) : Rat := if Rat.blt q 0 then -q else q

/-- Cauchy's estimate for a polynomial given by its coefficients from degree zero, the last
of which is the leading coefficient and does not vanish: one plus the sum of the absolute
values of the other coefficients divided by the absolute value of the last, rounded up. -/
def radius (p : List Rat) : Nat :=
  let lead := absQ (p.getLastD 1)
  let lower := p.dropLast.foldl (fun s c => s + absQ c) 0
  (1 + lower / lead).ceil.toNat

/-- The natural number a rational number is, if it is one, and zero otherwise. -/
def natBound (q : Rat) : Nat := if q.den == 1 then q.num.toNat else 0

/-- The two bounds of the rational numbers: the natural number itself, and Cauchy's estimate
for the natural numbers that are roots of a polynomial. -/
instance natBoundRat : NatBound ℚ where
  natBound := natBound
  natRootBound p := radius p.coeffs

end SympyProofs.Calculus.Antiderivative.Rational
