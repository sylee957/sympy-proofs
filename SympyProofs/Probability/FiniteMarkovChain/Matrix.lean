import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Semigroup
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Reachable

/-!
# The matrices of a continuous-time Markov chain

This folder is about matrices and row vectors only. No probability space appears in
it.

`Generator` defines generators, `IsGenerator`, and their transition matrices
`transition Q t = exp (t • Q)`, and proves that these are row stochastic.

`Semigroup` goes the other way: a semigroup of row-stochastic matrices that is
continuous at time `0` consists of the transition matrices of exactly one generator.

`Reachable` says when one state can be reached from another, and proves that a state
reachable from every state is reachable from all of them in one common time. It also
proves that reachability can be read off the generator: one state can be reached from
another exactly when a chain of positive rates leads from the one to the other.

The stationary distribution of a generator and the limit of its transition matrices
are in the folder `LongRun`.
-/
