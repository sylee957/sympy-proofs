module

public import SympyProofs.Gosper.RationalSum.Algorithm

/-! Rational-function interpretation of the compact output. -/

@[expose] public section
noncomputable section

namespace Gosper.RationalSum

open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Translate the numerator and denominator by the same amount. -/
def ShiftSum.fractionAt (s : ShiftSum K) (h : K) : RatFunc K :=
  (taylor h s.numerator : RatFunc K) /
    (taylor h (s.denominator.map (algebraMap ℚ K)) : RatFunc K)

/-- Expansion of a compact certificate term, with an optional outer shift. -/
def ShiftSum.expandAt (s : ShiftSum K) (h : K) : RatFunc K :=
  ∑ t ∈ Finset.range s.length, s.fractionAt (h + (t : K))

/-- The compact representation telescopes without expanding its shift interval. -/
theorem ShiftSum.expandAt_step (s : ShiftSum K) (h : K) :
    s.expandAt (h + 1) - s.expandAt h =
      s.fractionAt (h + (s.length : K)) - s.fractionAt h := by
  simp only [ShiftSum.expandAt, ← Finset.sum_sub_distrib]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
    add_assoc, add_left_comm, add_comm] using
    (Finset.sum_range_sub (fun t : ℕ => s.fractionAt (h + (t : K))) s.length)

/-- Residual fractions at orders `1, …, numerators.size`. -/
def Residual.expand (r : Residual K) : RatFunc K :=
  ∑ k : Fin r.numerators.size,
    (r.numerators[k.val] : RatFunc K) /
      (r.base.map (algebraMap ℚ K) : RatFunc K) ^ (k.val + 1)

/-- The rational certificate `G(X+h)`. -/
def Result.primitiveAt (r : Result K) (h : K) : RatFunc K :=
  (taylor h r.polynomial : RatFunc K) +
    (r.rational.map fun s => s.expandAt h).sum

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
