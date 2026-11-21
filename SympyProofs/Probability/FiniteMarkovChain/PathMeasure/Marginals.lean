module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Basic

/-!
# One-time distributions of the law of the chain

Under `chainLaw Q p` the state at time `t` has the law `p.bind (step Q t)`. In
particular the state at time zero has the law `p`, and it is in state `i` with
probability `p i`, which is `chainLaw_real_initial`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical Matrix

variable {ι : Type*} [MeasurableSpace ι] [Fintype ι] [DecidableEq ι]

section Marginal

variable (Q : Matrix ι ι ℝ)

/-- The distribution of the coordinate at time `t` is the initial law followed
by the transition PMF for duration `t`. -/
theorem chainLaw_coordinate (p : PMF ι) (t : ℝ≥0) :
    (chainLaw Q p).map (coordinate t) = (p.bind (step Q t)).toMeasure := by
  let I : Finset ℝ≥0 := {t}
  let ev : (I → ι) → ι := fun x => x ⟨t, by simp [I]⟩
  have hev : Measurable ev := measurable_pi_apply _
  have h := congrArg (Measure.map ev) (chainLaw_isProjectiveLimit Q p I)
  rw [Measure.map_map hev (Finset.measurable_restrict I), PMF.toMeasure_map _ _ hev] at h
  change (chainLaw Q p).map (coordinate t) = _ at h
  rw [h]
  congr 1
  simp [finiteLaw, sampledPath, I, sampleFuture, PMF.map_bind, ev,
    Finset.restrict, PMF.pure_map, PMF.bind_pure]

@[simp] theorem chainLaw_initial (p : PMF ι) :
    (chainLaw Q p).map (coordinate 0) = p.toMeasure := by
  rw [chainLaw_coordinate]
  have hz : step Q 0 = PMF.pure := funext (step_zero Q)
  rw [hz, PMF.bind_pure]

variable [MeasurableSingletonClass ι]

/-- Under the law of the chain from `p`, the state at time `0` is `i` with probability
`p i`. -/
theorem chainLaw_real_initial (p : PMF ι) (i : ι) :
    (chainLaw Q p).real {ω | coordinate 0 ω = i} = (p i).toReal := by
  have h : (chainLaw Q p).map (coordinate 0) {i} = p.toMeasure {i} := by
    rw [chainLaw_initial]
  rw [Measure.map_apply (measurable_coordinate 0) (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)] at h
  rw [measureReal_def]
  exact congrArg ENNReal.toReal h

end Marginal

end SympyProofs.FiniteMarkovChain
