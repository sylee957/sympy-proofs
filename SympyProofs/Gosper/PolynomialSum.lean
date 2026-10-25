module

public import SympyProofs.Gosper.PolynomialSum.Algorithm
public import SympyProofs.Gosper.PolynomialSum.Correctness

/-!
# Polynomial summation over rational algebras

`PolynomialSum.Algorithm` contains the executable coefficient recurrence and
polynomial constructor. `PolynomialSum.Correctness` proves their soundness,
finite-sum identities, degree bounds, and compatibility with specialization.

The main soundness theorem is `Gosper.PolynomialSum.antidifferenceOfFn_sound`:
for input `p = Polynomial.ofFn N a`, the computed `q = antidifferenceOfFn a`
satisfies `q.comp (1 + X) - q = p` and `q.eval 0 = 0`.

`Gosper.PolynomialSum.sum_range_antidifferenceCoefficients` connects the executable
coefficient vector to the finite sum after specialization. The `_apply` corollary
permits arbitrary functions of parameters as coefficients.
-/
