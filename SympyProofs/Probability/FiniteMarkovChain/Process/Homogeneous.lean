module

public import SympyProofs.Probability.FiniteMarkovChain.Process.Conditional

/-!
# Time homogeneity in two forms

This file is about time homogeneity alone: the chance of moving from a state `i` to a
state `j` over a duration `h` does not depend on when the move starts. It states this in
two ways and proves that they are equivalent.

* `HomogeneousConditional X P`:
  `P(X (s + h) = j | X s = i) = P(X (s' + h) = j | X s' = i)`, for any two starting
  times `s` and `s'`.
* `HomogeneousProduct X P`: the same, multiplied out as a product.

The form with conditional probabilities is asked only when the events that are
conditioned on have positive probability. The product form has no division and needs no
such condition.

The two forms are equivalent, by `homogeneousConditional_iff_homogeneousProduct`.

Many textbooks compare every starting time with time `0` only:
`P(X (s + h) = j | X s = i) = P(X h = j | X 0 = i)`. For a single process with a fixed
start this is weaker, because it says nothing about a state that cannot occur at time
`0`. Such a state could follow different rules at different times. For example, take
three states `a`, `b`, `c`. Start in `a`, leave `a` at rate `1` to `b` or `c` with
probability `1 / 2` each, and flip between `b` and `c` at a rate that grows with time.
The comparison with time `0` holds, but the way the process leaves `b` depends on the
time. So this file compares any two times. The example is not formalised here.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}

/-! ### The two forms -/

/-- Time homogeneity with conditional probabilities: the chance of moving from `i` to
`j` over a duration `h` is the same from any two times `s` and `s'`. -/
def HomogeneousConditional (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (s s' h : ℝ≥0) (i j : ι),
    P {ω | X s ω = i} ≠ 0 → P {ω | X s' ω = i} ≠ 0 →
    P[{ω | X (s + h) ω = j} | {ω | X s ω = i}] =
      P[{ω | X (s' + h) ω = j} | {ω | X s' ω = i}]

/-- Time homogeneity as a product of probabilities: the equation of
`HomogeneousConditional` multiplied by `P {X s = i} * P {X s' = i}`. -/
def HomogeneousProduct (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (s s' h : ℝ≥0) (i j : ι),
    P {ω | X s ω = i ∧ X (s + h) ω = j} * P {ω | X s' ω = i} =
      P {ω | X s' ω = i ∧ X (s' + h) ω = j} * P {ω | X s ω = i}

/-! ### Conditional and product forms -/

section

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure P]

/-- The product form gives the form with conditional probabilities. -/
theorem HomogeneousProduct.homogeneousConditional (hX : ∀ t, Measurable (X t))
    (h : HomogeneousProduct X P) : HomogeneousConditional X P := by
  intro s s' d i j hs hs'
  rw [cond_state hX, cond_state hX,
    inv_mul_eq_inv_mul_iff hs (measure_ne_top P _) hs' (measure_ne_top P _)]
  exact (h s s' d i j).trans (mul_comm _ _)

/-- The form with conditional probabilities gives the product form. -/
theorem HomogeneousConditional.homogeneousProduct (hX : ∀ t, Measurable (X t))
    (h : HomogeneousConditional X P) : HomogeneousProduct X P := by
  intro s s' d i j
  by_cases hs : P {ω | X s ω = i} = 0
  · have hA : P {ω | X s ω = i ∧ X (s + d) ω = j} = 0 :=
      measure_mono_null (fun ω hω => hω.1) hs
    rw [hA, hs, zero_mul, mul_zero]
  by_cases hs' : P {ω | X s' ω = i} = 0
  · have hA : P {ω | X s' ω = i ∧ X (s' + d) ω = j} = 0 :=
      measure_mono_null (fun ω hω => hω.1) hs'
    rw [hA, hs', zero_mul, mul_zero]
  · have := h s s' d i j hs hs'
    rw [cond_state hX, cond_state hX,
      inv_mul_eq_inv_mul_iff hs (measure_ne_top P _) hs' (measure_ne_top P _)] at this
    exact this.trans (mul_comm _ _)

/-- The conditional and product forms of time homogeneity are equivalent. -/
theorem homogeneousConditional_iff_homogeneousProduct (hX : ∀ t, Measurable (X t)) :
    HomogeneousConditional X P ↔ HomogeneousProduct X P :=
  ⟨fun h => h.homogeneousProduct hX, fun h => h.homogeneousConditional hX⟩

end

end SympyProofs.FiniteMarkovChain
