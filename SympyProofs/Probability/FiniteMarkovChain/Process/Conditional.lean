module

public import Mathlib.Probability.ConditionalProbability

/-!
# Conditional probability of a state as a ratio

Two small facts used to pass between a statement with conditional probabilities and the
same statement multiplied out.

`cond_state` writes the conditional probability that the state at time `t` is `j`, given
an event `A`, as the ratio `P (A ∩ {X t = j}) / P A`. It needs the process to be
measurable.

`inv_mul_eq_inv_mul_iff` says that two ratios are equal exactly when the cross products
are, provided the two denominators are neither zero nor infinite.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Two ratios are equal exactly when the cross products are. -/
theorem inv_mul_eq_inv_mul_iff {a b c d : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ∞)
    (hc : c ≠ 0) (hc' : c ≠ ∞) : b⁻¹ * a = c⁻¹ * d ↔ a * c = b * d := by
  constructor
  · intro h
    calc a * c = b * (b⁻¹ * a) * c := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hb hb', one_mul]
      _ = b * (c⁻¹ * d) * c := by rw [h]
      _ = b * d * (c⁻¹ * c) := by ring
      _ = b * d := by rw [ENNReal.inv_mul_cancel hc hc', mul_one]
  · intro h
    calc b⁻¹ * a = b⁻¹ * (a * c) * c⁻¹ := by
          rw [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel hc hc', mul_one]
      _ = b⁻¹ * (b * d) * c⁻¹ := by rw [h]
      _ = (b⁻¹ * b) * (c⁻¹ * d) := by ring
      _ = c⁻¹ * d := by rw [ENNReal.inv_mul_cancel hb hb', one_mul]

variable {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {X : ℝ≥0 → Ω → ι} {P : Measure Ω}

/-- The conditional probability of a state at time `t`, written out. -/
theorem cond_state (hX : ∀ t, Measurable (X t)) (A : Set Ω) (t : ℝ≥0) (j : ι) :
    P[{ω | X t ω = j} | A] = (P A)⁻¹ * P (A ∩ {ω | X t ω = j}) :=
  cond_apply' (hX t (measurableSet_singleton j)) P

end SympyProofs.FiniteMarkovChain
