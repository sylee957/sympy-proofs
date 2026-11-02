module

public import SympyProofs.Sum.Gosper.Hypergeometric
public import SympyProofs.Sum.Gosper.Nonsummable
public import SympyProofs.Sum.Gosper.Applications
public import SympyProofs.Sum.Gosper.Binomial
public import SympyProofs.Sum.Gosper.Cubic
public import SympyProofs.Sum.Gosper.Algorithm

/-!
# Gosper's indefinite hypergeometric summation theorem

Formalization of R. W. Gosper, *Decision procedure for indefinite hypergeometric
summation*, PNAS 75 (1978), 40–42, DOI: 10.1073/pnas.75.1.40.

The main theorem is `Gosper.hypergeometric_gosper_criterion`. Normalization is
provided by `Gosper.exists_normalForm`; `Gosper.exists_normalized_criterion`
combines normalization and the finite linear-system reduction. Numerical
finite sums follow from `Gosper.certificate_sum` and the product-sum theorems.
`Gosper.HasHypergeometricAntidifference ρ` uses the forward term ratio
`ρ(X) = a(X+1)/a(X)` and a forward sum ratio `σ(X) = S(X+1)/S(X)`.

`Algorithm.gosperTerm backend P Q` normalizes the forward ratio `P/Q`
directly over an integral domain `L`. `TermBackend K L` supplies normalization
operations over `L`, linear elimination over the constant domain `K`, and
optional coefficient descent from `L` to `K`. Normalization keeps nonmonic
polynomials and uses gcd and exact division. It constructs the shift resultant
and extracts natural roots using supplied arithmetic operations.
Its ratio identity holds over the ring; shift-coprimality is interpreted in
the fraction field.

`Algorithm.gosperSolve backend A B C` starts from the normalized equation
`A*x(X+1) - B*x = C`. Its degree bound uses an integer-ratio test over `K`.
The matrix entries lie in `K`; `C` and the output
lie in a commutative `K`-algebra. Fraction-free reduction of `[M | I]` records
row operations, pivot coefficients, and residual equations. Its nonzero scalar
denominator is retained in the candidate, so no division in the parameter ring
or parameter-coefficient equality test is needed during linear solving.

`Algorithm.Correctness` proves the multiplier identity and finite-sum formula.
`Algorithm.Completeness` characterizes summability by a returned candidate with
vanishing residual, conditional on successful coefficient descent.
`Algorithm.Specialization` transports these results through parameter evaluation,
including degree drops and newly vanishing residuals. Constants from `K` must
embed in the target field, and the specialized denominators must stay nonzero.

For field backends, `TermBackend.self` supplies identity coefficient descent
and uses `Backend.toNormalization` and `Backend.toLinear`. Correctness assumes
the supplied primitive contracts; no external implementation is trusted by them.
The definitions remain mathematical algorithm models where their underlying
polynomial operations are noncomputable.
-/
