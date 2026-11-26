module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split

/-! Clearing denominators in the last generator of a flat field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Numerators over a shared nonzero denominator in the last generator. -/
def commonDen : List (K R (n + 1)) → List (Poly (K R n)) × Poly (K R n)
  | [] => ([], 1)
  | x :: xs =>
    let (a, b) := x.split
    let (ps, d) := commonDen xs
    (a * d :: ps.map (· * b), b * d)

end SympyProofs.Calculus.Antiderivative
