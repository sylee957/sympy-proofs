module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field
public import SympyProofs.Calculus.Antiderivative.Program.Linear

/-! Rational residues of a parametric numerator over a factored squarefree denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

variable {F : Type} [Field F] [DecidableEq F]

/-- Equations in the rational combination coefficients and one rational residue at a factor.
The last column subtracts the residue times the differential derivative of the denominator.
Reading each coefficient of the remainders imposes divisibility by the factor. -/
def residueEquations (relations : List F → List (List ℚ)) (p ds : Poly F)
    (as : List (Poly F)) : List (List ℚ) :=
  let columns := (as ++ [-ds]).map (· % p)
  (List.range p.natDegree).flatMap fun j => relations (columns.map (·.coeff j))

/-- Rational coefficient combinations having rational residue at each supplied irreducible
normal factor. Each auxiliary residue is eliminated over the rationals. -/
def factoredResidueRows (relations : List F → List (List ℚ)) (factors : List (Poly F))
    (ds : Poly F) (as : List (Poly F)) : List (List ℚ) :=
  factors.flatMap fun p => Linear.eliminate as.length (residueEquations relations p ds as)

end SympyProofs.Calculus.Antiderivative.Step
