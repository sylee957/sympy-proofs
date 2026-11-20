module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.FiniteLaws
public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Extension

/-!
# The path measure

A path assigns a state to every time, so the sample space is `ℝ≥0 → ι` with the
product sigma-algebra. The random variable at time `t` is evaluation at `t`.

`pathMeasure Q d p` is the law of the chain on this space, for the matrix `Q` and the
initial distribution `p`. It is built from the finite laws in `FiniteLaws` by the
extension in `Extension`. `MarkovLaw` shows that, for a generator, the coordinate
process under it is a time-homogeneous Markov process with the transition
probabilities of `Q`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

variable {ι : Type*} [MeasurableSpace ι]

/-- The canonical sample space. Its measurable space is the product sigma-algebra. -/
abbrev Path (ι : Type*) := ℝ≥0 → ι

/-- The coordinate random variable at time `t`. -/
def coordinate (t : ℝ≥0) (ω : Path ι) : ι := ω t

@[fun_prop] theorem measurable_coordinate (t : ℝ≥0) : Measurable (coordinate (ι := ι) t) :=
  measurable_pi_apply t

variable [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (d : ι)

/-- The law on paths of the chain that starts from `p` and moves with the transition
laws `step Q`. The state `d` fills the times that a finite law does not observe. -/
noncomputable def pathMeasure (p : PMF ι) : Measure (Path ι) :=
  finiteProjectiveLimit (finiteLaw_isProjectiveMeasureFamily Q d p)

theorem pathMeasure_isProjectiveLimit (p : PMF ι) :
    IsProjectiveLimit (pathMeasure Q d p) (fun I => (finiteLaw Q d p I).toMeasure) :=
  finiteProjectiveLimit_isProjectiveLimit _

instance pathMeasure_isProbabilityMeasure (p : PMF ι) :
    IsProbabilityMeasure (pathMeasure Q d p) :=
  (pathMeasure_isProjectiveLimit Q d p).isProbabilityMeasure

end SympyProofs.FiniteMarkovChain
