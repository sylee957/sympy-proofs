module

public import SympyProofs.Binomial.Costs.FullAsymptotics
public import SympyProofs.Binomial.Costs.KaratsubaAsymptotics

/-!
# Binomial cost analysis

Algorithm-specific instrumentation and bounds live in this directory. Reusable
Python operation models and composition rules live in `SympyProofs.Python.Cost`.
`FullAsymptotics` proves a uniform quadratic upper bound on the actual complete
`primeExponentsM` counter under the declared schoolbook policy. The proof includes
the lazy sieve, integer arithmetic, allocation payload, product tree and shift.
`KaratsubaAsymptotics` proves `O(n^(log 3 / log 2))` for the same generated
execution under a policy with Karatsuba multiplication charges.
-/
