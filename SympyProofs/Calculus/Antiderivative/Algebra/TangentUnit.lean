module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor
public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field

/-! Recover an imaginary unit from the factorization of its defining quadratic. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable (F : Type) [Field F] [DecidableEq F] [ConstantFactors F]

/-- The negative constant coefficient of the first monic factor of X²+1.
Whenever the field contains an imaginary unit, this is one of its two roots. -/
def tangentUnit : F :=
  -((ConstantFactors.factors (Poly.X^2 + 1 : Poly F)).headD 0).coeff 0

end SympyProofs.Calculus.Antiderivative.Trigonometric
