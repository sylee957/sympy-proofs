import SympyProofs.Probability.FiniteMarkovChain.Process.Conditional
import SympyProofs.Probability.FiniteMarkovChain.Process.MarkovProperty
import SympyProofs.Probability.FiniteMarkovChain.Process.Homogeneous
import SympyProofs.Probability.FiniteMarkovChain.Process.Continuous
import SympyProofs.Probability.FiniteMarkovChain.Process.Basic
import SympyProofs.Probability.FiniteMarkovChain.Process.Bundled
import SympyProofs.Probability.FiniteMarkovChain.Process.Transition
import SympyProofs.Probability.FiniteMarkovChain.Process.Generator

/-!
# Time-homogeneous Markov processes

This folder is about a process `X t : Ω → ι` on a probability space `(Ω, P)`.

`MarkovProperty` is about the Markov property alone. It states it with conditional
probabilities, as textbooks do, and as a product of probabilities, and proves that the
two forms are equivalent.

`Homogeneous` does the same for time homogeneity.

`Continuous` does the same for the property that the process does not leave its state
instantly. It also proves that a process with right-continuous paths has this property.

`Conditional` holds two small facts used to pass between a conditional probability and
a product.

`Basic` states what it means for a process to be a time-homogeneous Markov process,
`IsHomogeneousMarkovProcess`. It mentions no matrix.

`Bundled` packs a probability space and a process on it into one object, `Process ι`,
for statements that say "some process" or "every process". It assumes nothing about
how the process moves.

`Transition` states what it means for a matrix to give the transition probabilities
of a process, `HasTransition`. Such a matrix is determined at the row of every state
that the process visits.

`Generator` proves that every time-homogeneous Markov process has the transition
probabilities of a generator, and that the generator is unique when every state is
visited at some time. It uses `Matrix.Semigroup`.

The stationary law and the limiting law of a process are in the folder `LongRun`.

The converse of `Generator`, that every generator has such a process, needs a
construction of the process. It is `exists_process_of_isGenerator` in
`PathMeasure.Existence`.
-/
