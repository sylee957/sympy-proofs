module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants
public import SympyProofs.Calculus.Antiderivative.Proof.Rat

/-! Correctness of the bounds on constants at the bottom of a tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K

/-- Rational bounds give bounds for the fractions of integers at height zero. -/
instance lawfulNatBoundInt : LawfulNatBound (K ℤ 0) :=
  LawfulNatBound.ofEquiv (constantsEquiv ℚ)

/-- Bounds on a field give bounds for fractions over it at height zero. -/
instance lawfulNatBoundField {F : Type} [Field F] [DecidableEq F] [NatBound F]
    [LawfulNatBound F] : LawfulNatBound (K F 0) :=
  LawfulNatBound.ofEquiv (constantsEquiv F)

end SympyProofs.Calculus.Antiderivative.K
