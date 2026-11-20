module

public import SympyProofs.Probability.FiniteMarkovChain.Process.Conditional

/-!
# The Markov property in two forms

This file is about the Markov property alone. It states it in two ways and proves that
they say the same thing.

In both, the past is a finite set `F` of earlier times with a state `x u` for each of
them, and `s < t` are two times later than all of them.

`MarkovPropertyConditional X P` is the textbook form:

`P(X t = j | X u = x u for all u in F, and X s = i) = P(X t = j | X s = i)`.

Given the present state, the past gives no further information about the future. The
left side is a conditional probability, so the equation is asked only when the event
that is conditioned on has positive probability.

`MarkovPropertyProduct X P` is the same equation multiplied out. It has no division, so
it needs no condition on probabilities.

`markovPropertyConditional_iff_markovPropertyProduct` proves that the two are
equivalent. One direction divides by two probabilities that are not zero. In the other,
both sides of the product form are zero when the conditioning event has probability
zero.

`Basic` uses the product form as the Markov property of a time-homogeneous Markov
process, because the proofs need an equation that holds with no condition.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {ι Ω : Type*} {X : ℝ≥0 → Ω → ι}

/-- Observing one more time is an intersection of events. -/
private theorem past_inter (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s t : ℝ≥0) (i j : ι) :
    {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} =
      {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} ∩ {ω | X t ω = j} := by
  ext ω
  exact and_assoc.symm

/-! ### The two forms -/

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The Markov property with conditional probabilities: given the states `x u` at the
earlier times `u ∈ F` and the state `i` at time `s`, the state at a later time `t`
depends only on `i`. -/
def MarkovPropertyConditional (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s t : ℝ≥0) (i j : ι),
    (∀ u ∈ F, u < s) → s < t →
    P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} ≠ 0 →
    P[{ω | X t ω = j} | {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i}] =
      P[{ω | X t ω = j} | {ω | X s ω = i}]

/-- The Markov property as a product of probabilities: the equation of
`MarkovPropertyConditional` multiplied by `P {past and X s = i} * P {X s = i}`. -/
def MarkovPropertyProduct (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s t : ℝ≥0) (i j : ι),
    (∀ u ∈ F, u < s) → s < t →
    P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} * P {ω | X s ω = i} =
      P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} * P {ω | X s ω = i ∧ X t ω = j}

/-! ### Equivalence -/

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable [IsFiniteMeasure P]

/-- The product form gives the form with conditional probabilities. -/
theorem MarkovPropertyProduct.markovPropertyConditional (hX : ∀ t, Measurable (X t))
    (h : MarkovPropertyProduct X P) : MarkovPropertyConditional X P := by
  intro F x s t i j hF hst hB
  have hci : P {ω | X s ω = i} ≠ 0 := fun h0 =>
    hB (measure_mono_null (fun ω hω => hω.2) h0)
  have hp := h F x s t i j hF hst
  rw [past_inter] at hp
  rw [cond_state hX, cond_state hX,
    inv_mul_eq_inv_mul_iff hB (measure_ne_top P _) hci (measure_ne_top P _)]
  exact hp

/-- The form with conditional probabilities gives the product form. -/
theorem MarkovPropertyConditional.markovPropertyProduct (hX : ∀ t, Measurable (X t))
    (h : MarkovPropertyConditional X P) : MarkovPropertyProduct X P := by
  intro F x s t i j hF hst
  rw [past_inter]
  by_cases hB : P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} = 0
  · have hA : P ({ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} ∩ {ω | X t ω = j}) = 0 :=
      measure_mono_null Set.inter_subset_left hB
    rw [hA, hB, zero_mul, zero_mul]
  · have hci : P {ω | X s ω = i} ≠ 0 := fun h0 =>
      hB (measure_mono_null (fun ω hω => hω.2) h0)
    have := h F x s t i j hF hst hB
    rwa [cond_state hX, cond_state hX,
      inv_mul_eq_inv_mul_iff hB (measure_ne_top P _) hci (measure_ne_top P _)] at this

/-- The two forms of the Markov property are equivalent. -/
theorem markovPropertyConditional_iff_markovPropertyProduct (hX : ∀ t, Measurable (X t)) :
    MarkovPropertyConditional X P ↔ MarkovPropertyProduct X P :=
  ⟨fun h => h.markovPropertyProduct hX, fun h => h.markovPropertyConditional hX⟩

end SympyProofs.FiniteMarkovChain
