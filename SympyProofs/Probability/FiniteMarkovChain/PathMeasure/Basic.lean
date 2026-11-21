module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.FiniteLaws
public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Extension

/-!
# The law of the chain on paths

A path assigns a state to every time, so the sample space is `ℝ≥0 → ι` with the
product sigma-algebra. The random variable at time `t` is evaluation at `t`.

`chainLaw Q p` is the law of the chain on this space, for the matrix `Q` and the
initial distribution `p`. It is built from the finite laws in `FiniteLaws` by the
extension in `Extension`. `MarkovLaw` shows that, for a generator, the coordinate
process under it is a time-homogeneous Markov process with the transition
probabilities of `Q`.

The finite laws need a state to fill the times that they do not observe. That state is
`filler p`. It is the same state for every `p`, by `filler_eq`, and it has no effect on
the law, so it appears in no statement outside this construction.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

/-- A state that fills the times a finite law does not observe. The argument `p` only
shows that a state exists. -/
noncomputable def filler {ι : Type*} (p : PMF ι) : ι :=
  Classical.choice ⟨p.support_nonempty.some⟩

/-- The filler is the same state for every `p`. -/
theorem filler_eq {ι : Type*} (p p' : PMF ι) : filler p = filler p' := rfl

variable {ι : Type*} [MeasurableSpace ι]

/-- The canonical sample space. Its measurable space is the product sigma-algebra. -/
abbrev Path (ι : Type*) := ℝ≥0 → ι

/-- The coordinate random variable at time `t`. -/
def coordinate (t : ℝ≥0) (ω : Path ι) : ι := ω t

@[fun_prop] theorem measurable_coordinate (t : ℝ≥0) : Measurable (coordinate (ι := ι) t) :=
  measurable_pi_apply t

variable [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)

/-- The law on paths of the chain that starts from `p` and moves with the transition
laws `step Q`. -/
noncomputable def chainLaw (p : PMF ι) : Measure (Path ι) :=
  finiteProjectiveLimit (finiteLaw_isProjectiveMeasureFamily Q (filler p) p)

theorem chainLaw_isProjectiveLimit (p : PMF ι) :
    IsProjectiveLimit (chainLaw Q p) (fun I => (finiteLaw Q (filler p) p I).toMeasure) :=
  finiteProjectiveLimit_isProjectiveLimit _

instance chainLaw_isProbabilityMeasure (p : PMF ι) : IsProbabilityMeasure (chainLaw Q p) :=
  (chainLaw_isProjectiveLimit Q p).isProbabilityMeasure

end SympyProofs.FiniteMarkovChain
