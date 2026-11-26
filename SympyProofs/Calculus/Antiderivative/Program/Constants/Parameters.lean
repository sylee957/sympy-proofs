module

public import SympyProofs.Calculus.Antiderivative.Program.Residue
public import SympyProofs.Calculus.Antiderivative.Program.LogRelations
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Tower
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Rational
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Recognize

/-! Rational function fields used as the constants of another differential tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The computable field of rational functions in independent constant parameters over ℚ. -/
abbrev Parameters (m : ℕ) := K ℤ m

/-- Find natural numbers among parameter-dependent constants by exact constant recognition.
For roots of a polynomial, use the squarefree modulus of its parameter-independent roots. -/
instance (m : ℕ) : NatBound (Parameters (m + 1)) where
  natBound a := (a.const?.map NatBound.natBound).getD 0
  natRootBound p := NatBound.natRootBound (Residue.constantRoots p)

/-- Clearing denominators and collecting parameter monomials gives rational dependencies. -/
instance (m : ℕ) : IntegerRelations (Parameters (m + 1)) := ⟨rationalRows⟩

/-- Factor over the independent parameters using the ground rational factorization. -/
instance (m : ℕ) : ConstantFactors (Parameters (m + 1)) := ⟨factorTower⟩

end SympyProofs.Calculus.Antiderivative
