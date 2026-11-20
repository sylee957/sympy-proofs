import SympyProofs.Probability.FiniteMarkovChain.Process.Conditional
import SympyProofs.Probability.FiniteMarkovChain.Process.MarkovProperty
import SympyProofs.Probability.FiniteMarkovChain.Process.Homogeneous
import SympyProofs.Probability.FiniteMarkovChain.Process.Continuous
import SympyProofs.Probability.FiniteMarkovChain.Process.Basic
import SympyProofs.Probability.FiniteMarkovChain.Process.Transition
import SympyProofs.Probability.FiniteMarkovChain.Process.Generator
import SympyProofs.Probability.FiniteMarkovChain.Process.Stationary
import SympyProofs.Probability.FiniteMarkovChain.Process.Limit

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

`Transition` states what it means for a matrix to give the transition probabilities
of a process, `HasTransition`. Such a matrix is determined at the row of every state
that the process visits.

`Generator` proves that every time-homogeneous Markov process has the transition
probabilities of a generator, and that the generator is unique when every state is
visited at some time. It uses `Matrix.Semigroup`.

`Stationary` shows that the balance equation is the condition for a process to keep
the same law at every time. It uses `Matrix.Stationary`.

`Limit` defines the limiting distribution of a process, `IsLimitingDistribution`. A
limiting distribution is a stationary distribution of the generator. When some state
can be reached from every state the converse holds. Every time-homogeneous Markov
process has exactly one limiting distribution. It uses `Matrix.Limit`.

The converse of `Generator`, that every generator has such a process, needs a
construction of the process. It is `exists_process_of_isGenerator` in
`PathMeasure.Existence`.
-/
