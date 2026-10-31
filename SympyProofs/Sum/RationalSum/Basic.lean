module

public import SympyProofs.Sum.RationalSum.Algorithm

/-! Rational-function interpretation of the compact output. -/

@[expose] public section
noncomputable section

namespace Gosper.RationalSum

open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Residual fractions at orders `1, …, numerators.size`. -/
def Residual.expand (r : Residual K) : RatFunc K :=
  ∑ k : Fin r.numerators.size,
    (r.numerators[k.val] : RatFunc K) /
      (r.base.map (algebraMap ℚ K) : RatFunc K) ^ (k.val + 1)

/-- The rational certificate `G(X+h)`. -/
def Result.primitiveAt (r : Result K) (h : K) : RatFunc K :=
  (taylor h r.polynomial : RatFunc K) +
    ∑ i : Fin r.rational.size,
      let s := r.rational[i.val]
      ∑ t ∈ Finset.range s.length,
        (taylor (h + (t : K)) s.numerator : RatFunc K) /
          (taylor (h + (t : K)) (s.denominator.map (algebraMap ℚ K)) : RatFunc K)

def Result.residualPart (r : Result K) : RatFunc K :=
  (r.residual.map Residual.expand).sum

/-- The residual-zero conditions can be retained symbolically and specialized. -/
def Result.residualVanishes (r : Result K) : Prop :=
  ∀ group ∈ r.residual, ∀ a ∈ group.numerators, a = 0

/-- The reconstruction identity proved for the reducer by `reduce_sound`. -/
def Result.Sound (r : Result K) (P : Polynomial K) (D : Polynomial ℚ) : Prop :=
  (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K) =
    r.primitiveAt 1 - r.primitiveAt 0 + r.residualPart

end Gosper.RationalSum
