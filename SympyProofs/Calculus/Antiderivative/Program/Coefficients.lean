module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.CommonDen

/-! Constant-linear equations on a list of field elements, obtained by clearing denominators
and extracting the coefficients of each generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- A row for each power appearing in the polynomials, in ascending degree order. -/
def coefficientSlices {F : Type} [Field F] [DecidableEq F] (ps : List (Poly F)) :
    List (List F) :=
  let width := (ps.map fun p => p.coeffs.length).max?.getD 0
  (List.range width).map fun i => ps.map (·.coeff i)

/-- Homogeneous equations over the constants saying a linear combination is zero. -/
def rowsOf : {n : ℕ} → List (K R n) → List (List (K R 0))
  | 0, ws => [ws]
  | _ + 1, ws => (coefficientSlices (commonDen ws).1).flatMap rowsOf

end SympyProofs.Calculus.Antiderivative
