module

public import SympyProofs.Gosper.PolynomialSum.Algorithm
public import SympyProofs.Gosper.PolynomialSum.Correctness

/-!
# Polynomial summation over rational algebras

`PolynomialSum.antidifference p` takes a polynomial directly and computes its
normalized antidifference using the coefficient recurrence in `Algorithm`.
`PolynomialSum.Correctness` proves its soundness,
finite-sum identities, degree bounds, and compatibility with specialization.

The main soundness theorem is `Gosper.PolynomialSum.antidifference_sound`:
for a polynomial input `p`, the computed `q = antidifference p`
satisfies `q.comp (1 + X) - q = p` and `q.eval 0 = 0`.

`sum_range_map` and `sum_range_apply` connect the computed polynomial to finite
sums after algebraic specialization or evaluation of arbitrary parameter functions.
The coefficient-vector interfaces remain available for inputs with explicit size
bounds, without coefficient zero tests in the recurrence.
-/
