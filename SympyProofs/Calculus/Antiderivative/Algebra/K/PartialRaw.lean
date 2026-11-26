module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Raw

/-! Computing a partial derivative directly on a flat numerator and denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K.Raw

variable {R : Type} [CommRing R] [DecidableEq R] [Div R] [NormalizedGCDMonoid R]

/-- Differentiate a fraction with respect to variable `i` by the quotient rule. -/
def pderiv (n i : ℕ) (x : Raw R) : Raw R :=
  let da := MPoly.Raw.partial n i x.num
  if polyEq n x.den (MPoly.Raw.C 1) then ofPoly da
  else
    let db := MPoly.Raw.partial n i x.den
    let num := MPoly.Raw.sub n (MPoly.Raw.mul n da x.den) (MPoly.Raw.mul n x.num db)
    cancel n num (MPoly.Raw.mul n x.den x.den)

end SympyProofs.Calculus.Antiderivative.K.Raw
