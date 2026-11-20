module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Basic

/-!
# One-time distributions of the path measure

Under `pathMeasure Q d p` the state at time `t` has the law `p.bind (step Q t)`. In
particular the state at time zero has the law `p`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical Matrix

variable {ι : Type*} [MeasurableSpace ι] [Fintype ι] [DecidableEq ι]

section Marginal

variable (Q : Matrix ι ι ℝ) (d : ι)

/-- The distribution of the coordinate at time `t` is the initial law followed
by the transition PMF for duration `t`. -/
theorem pathMeasure_coordinate (p : PMF ι) (t : ℝ≥0) :
    (pathMeasure Q d p).map (coordinate t) = (p.bind (step Q t)).toMeasure := by
  let I : Finset ℝ≥0 := {t}
  let ev : (I → ι) → ι := fun x => x ⟨t, by simp [I]⟩
  have hev : Measurable ev := measurable_pi_apply _
  have h := congrArg (Measure.map ev) (pathMeasure_isProjectiveLimit Q d p I)
  rw [Measure.map_map hev (Finset.measurable_restrict I), PMF.toMeasure_map _ _ hev] at h
  change (pathMeasure Q d p).map (coordinate t) = _ at h
  rw [h]
  congr 1
  simp [finiteLaw, sampledPath, I, sampleFuture, PMF.map_bind, ev,
    Finset.restrict, PMF.pure_map, PMF.bind_pure]

@[simp] theorem pathMeasure_initial (p : PMF ι) :
    (pathMeasure Q d p).map (coordinate 0) = p.toMeasure := by
  rw [pathMeasure_coordinate]
  have hz : step Q 0 = PMF.pure := funext (step_zero Q)
  rw [hz, PMF.bind_pure]

end Marginal

end SympyProofs.FiniteMarkovChain
