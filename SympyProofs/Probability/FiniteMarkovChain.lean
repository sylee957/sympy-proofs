import SympyProofs.Probability.FiniteMarkovChain.Matrix
import SympyProofs.Probability.FiniteMarkovChain.Process
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure

/-!
# Finite-state continuous-time Markov chain stationarity

The development has three parts. The first two have matching file names.

`Matrix` is about matrices only: generators and their transition matrices, the
balance equation, and convergence to its solution.

`Process` is about a process on a probability space: what a time-homogeneous Markov
process is, that it has a generator, when it keeps its law, and where its law goes.
Each of its results is the matrix result of the same name read on a process.

`PathMeasure` constructs a measure on the space of paths, and so shows that every
generator has a time-homogeneous Markov process with its transition probabilities. It
also shows that this measure is the only one for a given initial distribution, and
that the limiting distributions over all initial distributions are exactly the
stationary distributions of the generator. Nothing in the first two parts uses it.

The motivation is SymPy issue #30980 and PR #30981, which change the stationary
condition of a continuous-time chain from `w * Q = w` to `w * Q = 0`. The second
equation is `Balance Q w` in `Matrix.Stationary`. This development proves that it is
the condition for a process to keep its law, and that, when some state can be reached
from every state, its one solution of total mass one is the limit of the law of the
process from every start.

https://github.com/sympy/sympy/issues/30980
https://github.com/sympy/sympy/pull/30981
-/
