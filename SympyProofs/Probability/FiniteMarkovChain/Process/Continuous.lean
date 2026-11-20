module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Topology.Instances.ENNReal.Lemmas

import Mathlib.MeasureTheory.Integral.Indicator

/-!
# No instant jumps, in two forms

This file is about one property alone: the process does not leave its current state
instantly. If it is in state `i` now, then a very short time later it is still in `i`
with probability close to `1`. It states this in two ways and proves that they are
equivalent. It also proves that the property holds for a process with right-continuous
paths.

* `ContinuousConditional X P`: `P(X (s + h) = i | X s = i)` tends to `1` as `h` tends
  to `0`, at every time `s`.
* `ContinuousProduct X P`: the same, multiplied by `P {X s = i}`.

The form with a conditional probability is asked only when the state `i` has positive
probability at time `s`. The product form needs no such condition.

The two forms are equivalent, by `continuousConditional_iff_continuousProduct`.

Textbooks state this property for the transition function: the chance of staying in `i`
over a duration `h` tends to `1` as `h` tends to `0`, for every state `i`. Such a
transition function is called standard. For a single process with a fixed start, asking
this at time `0` only would be weaker, because it says nothing about a state that cannot
occur at time `0`. Such a state could be left instantly. So this file asks the property
at every time.

Many textbooks ask for more: that every path is right continuous. With a discrete state
space this means that after each time the path stays where it is for a positive time,
which is `HasRightContinuousPaths X`. It implies the property of this file, by
`HasRightContinuousPaths.continuousProduct`. The converse is false, because the forms
here only look at two times and cannot see what a single path does.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}

/-! ### The two forms -/

/-- No instant jumps, with a conditional probability: at every time `s`, given that the
state is `i`, the chance that it is still `i` after a duration `h` tends to `1`. -/
def ContinuousConditional (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (s : ℝ≥0) (i : ι), P {ω | X s ω = i} ≠ 0 →
    Tendsto (fun h : ℝ≥0 => P[{ω | X (s + h) ω = i} | {ω | X s ω = i}]) (𝓝 0) (𝓝 1)

/-- No instant jumps, multiplied out: the statement of `ContinuousConditional` times
`P {X s = i}`. -/
def ContinuousProduct (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (s : ℝ≥0) (i : ι),
    Tendsto (fun h : ℝ≥0 => P {ω | X s ω = i ∧ X (s + h) ω = i}) (𝓝 0)
      (𝓝 (P {ω | X s ω = i}))

/-- Every path stays in its state for a positive time after each time `s`. For a
discrete state space this is right continuity of the paths. -/
def HasRightContinuousPaths (X : ℝ≥0 → Ω → ι) : Prop :=
  ∀ (ω : Ω) (s : ℝ≥0), ∀ᶠ h in 𝓝 (0 : ℝ≥0), X (s + h) ω = X s ω

/-! ### Conditional and product forms -/

/-- A conditional probability tends to `1` exactly when the probability of both events
tends to the probability of the condition. -/
private theorem tendsto_cond_iff [IsFiniteMeasure P] {S : Set Ω} {T : ℝ≥0 → Set Ω}
    (hT : ∀ h, MeasurableSet (T h)) (hS : P S ≠ 0) :
    Tendsto (fun h => P[T h | S]) (𝓝 0) (𝓝 1) ↔
      Tendsto (fun h => P (S ∩ T h)) (𝓝 0) (𝓝 (P S)) := by
  have hc : ∀ h, P[T h | S] = (P S)⁻¹ * P (S ∩ T h) := fun h => cond_apply' (hT h) P
  simp_rw [hc]
  constructor
  · intro hl
    have := ENNReal.Tendsto.const_mul (a := P S) hl (Or.inr (measure_ne_top P _))
    rw [mul_one] at this
    refine this.congr fun h => ?_
    rw [← mul_assoc, ENNReal.mul_inv_cancel hS (measure_ne_top P _), one_mul]
  · intro hl
    have := ENNReal.Tendsto.const_mul (a := (P S)⁻¹) hl (Or.inr (ENNReal.inv_ne_top.2 hS))
    rwa [ENNReal.inv_mul_cancel hS (measure_ne_top P _)] at this

section

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure P]

/-- The product form gives the form with a conditional probability. -/
theorem ContinuousProduct.continuousConditional (hX : ∀ t, Measurable (X t))
    (h : ContinuousProduct X P) : ContinuousConditional X P := fun s i hs =>
  (tendsto_cond_iff (fun d => hX (s + d) (measurableSet_singleton i)) hs).2 (h s i)

/-- The form with a conditional probability gives the product form. -/
theorem ContinuousConditional.continuousProduct (hX : ∀ t, Measurable (X t))
    (h : ContinuousConditional X P) : ContinuousProduct X P := by
  intro s i
  by_cases hs : P {ω | X s ω = i} = 0
  · have hA : ∀ d : ℝ≥0, P {ω | X s ω = i ∧ X (s + d) ω = i} = 0 := fun d =>
      measure_mono_null (fun ω hω => hω.1) hs
    simp_rw [hA, hs]
    exact tendsto_const_nhds
  · exact (tendsto_cond_iff (fun d => hX (s + d) (measurableSet_singleton i)) hs).1
      (h s i hs)

/-- The conditional and product forms are equivalent. -/
theorem continuousConditional_iff_continuousProduct (hX : ∀ t, Measurable (X t)) :
    ContinuousConditional X P ↔ ContinuousProduct X P :=
  ⟨fun h => h.continuousProduct hX, fun h => h.continuousConditional hX⟩

/-! ### Right-continuous paths -/

/-- A process with right-continuous paths does not leave its state instantly. -/
theorem HasRightContinuousPaths.continuousProduct (hX : ∀ t, Measurable (X t))
    (h : HasRightContinuousPaths X) : ContinuousProduct X P := by
  intro s i
  refine tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure (𝓝 (0 : ℝ≥0)) P
    (fun d => (hX s (measurableSet_singleton i)).inter
      (hX (s + d) (measurableSet_singleton i))) fun ω => ?_
  exact (h ω s).mono fun d hd => ⟨fun a => a.1, fun a => ⟨a, hd.trans a⟩⟩

end

end SympyProofs.FiniteMarkovChain
