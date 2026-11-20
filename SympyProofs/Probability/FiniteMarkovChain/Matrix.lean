import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Semigroup
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Stationary
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Reachable
import SympyProofs.Probability.FiniteMarkovChain.Matrix.Limit
import SympyProofs.Probability.FiniteMarkovChain.Matrix.LimitMatrix
import SympyProofs.Probability.FiniteMarkovChain.Matrix.LimitEquation

/-!
# The matrices of a continuous-time Markov chain

This folder is about matrices and row vectors only. No probability space appears in
it. `Generator`, `Stationary`, and `Limit` each have a counterpart of the same name in
`Process`, which says the same thing for a process.

`Generator` defines generators, `IsGenerator`, and their transition matrices
`transition Q t = exp (t • Q)`, and proves that these are row stochastic.

`Semigroup` goes the other way: a semigroup of row-stochastic matrices that is
continuous at time `0` consists of the transition matrices of exactly one generator.

`Stationary` states the balance equation `w ᵥ* Q = 0` and proves that it holds exactly
when `w` is unchanged by every transition matrix. A stationary distribution,
`IsStationaryDistribution`, is a solution with nonnegative entries that sum to one.

`Reachable` says when one state can be reached from another, and proves that a state
reachable from every state is reachable from all of them in one common time. It also
proves that reachability can be read off the generator: one state can be reached from
another exactly when a chain of positive rates leads from the one to the other.

`Limit` proves that, when some state can be reached from every state, a stationary
distribution exists, it is the one solution of the balance equation with total mass
one, and the row `p ᵥ* transition Q t` converges to it. It also proves the converse of
uniqueness: a generator has exactly one stationary distribution exactly when some state
can be reached from every state. Without that condition the transition matrices still
converge, and the limit of the row is a stationary distribution that may depend on `p`.

`LimitMatrix` names the limit of the transition matrices, `limitMatrix Q`, and proves
its properties: its rows are stationary distributions, its columns are annihilated by
`Q`, and the limit of the row `p ᵥ* transition Q t` is `p ᵥ* limitMatrix Q`.

`LimitEquation` gives linear equations that determine that limit: the balance equation
together with one equation for each column `h` with `Q *ᵥ h = 0`. So the limit can be
computed with no limit and no matrix exponential.
-/
