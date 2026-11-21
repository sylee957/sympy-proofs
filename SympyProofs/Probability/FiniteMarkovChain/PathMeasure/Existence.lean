module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.MarkovLaw
public import SympyProofs.Probability.FiniteMarkovChain.Process.Bundled

/-!
# Every generator has a process

`Process.Generator` shows that a time-homogeneous Markov process has
the transition probabilities of a generator. This file is the converse. For every
generator `Q` and every initial distribution `p` there is a probability space with a
time-homogeneous Markov process on it that starts from `p` and has the transition
probabilities of `Q`. This is `exists_process_of_isGenerator`. The space and the process
are given together, as a `Process ι`.

The statement mentions no measure on paths. The proof uses one: the process is the
coordinate process on the space of paths, under `chainLaw Q p`. The rest of this
folder exists to construct that measure and to prove these properties of it.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory
open scoped NNReal

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- For every generator and every initial distribution there is a time-homogeneous
Markov process that starts from that distribution and has the transition probabilities
of the generator. -/
theorem exists_process_of_isGenerator {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) (p : PMF ι) :
    ∃ S : Process ι, S.P.map (S.X 0) = p.toMeasure ∧
      IsHomogeneousMarkovProcess S.X S.P ∧ HasTransition Q S.X S.P :=
  ⟨⟨Path ι, chainLaw Q p, coordinate⟩, chainLaw_initial Q p,
    chainLaw_isHomogeneousMarkovProcess hQ p, chainLaw_hasTransition hQ p⟩

end SympyProofs.FiniteMarkovChain
