module

public import SympyProofs.LinearAlgebra.NeumannSeries.Basic
public import SympyProofs.LinearAlgebra.NeumannSeries.Lyapunov
public import SympyProofs.LinearAlgebra.NeumannSeries.Sylvester
public import SympyProofs.LinearAlgebra.NeumannSeries.Algebraic
public import SympyProofs.LinearAlgebra.NeumannSeries.Polynomial
public import SympyProofs.LinearAlgebra.NeumannSeries.Rational
public import SympyProofs.LinearAlgebra.NeumannSeries.Complex
public import SympyProofs.LinearAlgebra.NeumannSeries.ComplexPolynomial
public import SympyProofs.LinearAlgebra.NeumannSeries.Spectrum
public import SympyProofs.LinearAlgebra.NeumannSeries.Weighted

/-!
# Matrix Neumann series: exact polynomial convergence conditions

For finite real square matrices, this development proves:

* convergence of ordinary partial sums iff summability iff matrix powers tend to zero;
* summability iff a positive definite solution of `P - Aᵀ P A = I` exists;
* uniqueness of the Stein equation whenever the powers tend to zero;
* Sylvester's criterion using the leading principal minors;
* `summable_pow_iff_algebraicCondition`: the exact finite determinant sign condition;
* `polynomial_convergence_iff`: construction over `MvPolynomial σ ℚ` commutes with evaluation;
* `rational_polynomial_convergence_iff`: the same result for a common-denominator
  presentation `N / c`, retaining the condition that the denominator is nonzero;
* the value of every convergent series is `(I - A)⁻¹`.

The coefficient matrix uses all `n²` coordinates of `P`. Its determinant `d` and
the matrix `R` obtained from its adjugate are polynomial expressions. The final
condition is `d ≠ 0` and `d^k * det (leading R k) > 0` for each leading minor.
Only finite index quantification remains; no auxiliary real variables or general
quantifier-elimination procedure occur. The empty minor has determinant one.

For complex matrices `A = X + iY`, realification `[[X,-Y],[Y,X]]` preserves powers
and summability and sends the conjugate transpose to the real transpose. Thus
`summable_complex_pow_iff_algebraicCondition` gives the same exact criterion after
doubling the matrix dimension. `complex_polynomial_convergence_iff` and
`complex_rational_polynomial_convergence_iff` express it as real polynomial signs
in the parameters of `X` and `Y`; the rational case uses a common real polynomial
denominator.

Polynomial weights do not change the condition: `summable_pow_mul_pow_iff_summable_pow`
shows that `∑ k ^ p * A ^ k` converges exactly when `∑ A ^ k` does. In spectral terms,
`summable_complex_pow_mul_pow_iff_spectrum` and `summable_pow_mul_pow_iff_spectrum` state
that this happens exactly when every complex eigenvalue has modulus less than one.

The weighted sums have closed forms whenever the series converges. `hasSum_choose_mul_pow`
gives `∑ (k + j).choose j * A ^ k = (I - A)⁻¹ ^ (j + 1)`, and `hasSum_pow_mul_pow` gives
`∑ k ^ p * A ^ k = ∑ j ≤ p, S(p, j) * j! * A ^ j * (I - A)⁻¹ ^ (j + 1)` with `S(p, j)` the
Stirling numbers of the second kind. The first cases are `hasSum_natCast_mul_pow`,
`∑ k * A ^ k = A * (I - A)⁻¹ ^ 2`, and `hasSum_sq_mul_pow`,
`∑ k ^ 2 * A ^ k = A * (I + A) * (I - A)⁻¹ ^ 3`.

These theorems formalize mathematical convergence conditions, not SymPy's Python
implementation.

Motivation: https://github.com/sympy/sympy/issues/14230
-/
