import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Step
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.FiniteLaws
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Extension
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Basic
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Marginals
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.MarkovLaw
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Existence
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Characterization
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Family
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Limit

/-!
# The law of the chain on paths

The law of the chain on the space of paths `ℝ≥0 → ι`.

The purpose of this folder is one statement, `exists_process_of_isGenerator` in
`Existence`: every generator has a time-homogeneous Markov process with its
transition probabilities. `Process` defines such processes and never produces one. The
law on paths is how one is produced. `Matrix` and `Process` use nothing from this
folder.

The paths are all functions from time to states. Nothing is proved about how a single
path looks, and right-continuous paths are not obtained.

`Basic` defines `chainLaw Q p`. `Step`, `FiniteLaws`, and `Extension` hold its
construction. `Step` gives the law of the next state as a probability mass function,
`FiniteLaws` samples the chain at finitely many times, and `Extension` extends those
laws to all times.

`Marginals` computes the law of the state at one time. `MarkovLaw` proves that the
coordinate process under that law is a time-homogeneous Markov process with
the transition probabilities of the generator.

`Characterization` proves that it is the only measure on paths with these properties
and a given initial distribution, `existsUnique_chainLaw`. A generator and an initial
distribution do not determine the process, but they determine its law on paths.

`Family` describes all the laws of one generator together, one for each initial
distribution. Each is a mixture of the laws from the single states, they match the
initial distributions one to one, and together they determine the generator.

`Limit` says where these laws go as time grows. The limiting distributions that occur
in the family are exactly the stationary distributions of the generator, and all
members have the same one exactly when some state can be reached from every state. It
uses `Process.Limit`.
-/
