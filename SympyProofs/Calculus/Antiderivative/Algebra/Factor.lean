module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field

/-! Univariate factorization in the ground constants used to identify rational residues. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Monic irreducible factors of a nonzero polynomial, listed with multiplicity. -/
class ConstantFactors (F : Type) [Zero F] where
  /-- The nonconstant monic factors over the input field. -/
  factors : Poly F → List (Poly F)

end SympyProofs.Calculus.Antiderivative
