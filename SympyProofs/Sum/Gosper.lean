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

`Algorithm.gosperTerm` models the procedure on Mathlib polynomials over a
characteristic-zero coefficient field with decidable `IsLocalization.IsInteger ℤ`
membership. `Encodable.choose` recovers integer witnesses constructively; a rational
instance decides membership by checking the reduced denominator. A `Backend`
supplies factorization, resultant, zero matrices, entry updates, column reads, and RREF;
shift resultants, natural integer roots, and linear solving
are derived from them. `Algorithm.gosperSolve backend A B C` starts directly
from `A*x(X+1) - B*x = C`, where `B` is already shifted backward from the
normal form. `A` and `B` determine matrix entries over `K`; `C` may have
coefficients in a commutative `K`-algebra. RREF and all inversions stay over `K`.
An optional final bound `N` fixes the matrix dimensions; omitting it uses
`C.natDegree`. With the same `N` on both sides, `Algorithm.gosperSolve_map`
proves that the actual solver commutes with parameter specialization, including
noninjective evaluation maps and drops in degree.
For a returned result, `Algorithm.gosperSolve_specialize_complete` characterizes
the solvable specialized polynomial equations by the evaluated residual conditions,
including a zero specialized right-hand side. `Algorithm.gosperSolve_specialize_ratFunc` gives
the corresponding rational multiplier identity directly from normalized inputs.
The coefficient matrix is augmented by an identity matrix
to record reusable row operations. One matrix-vector product applies its right
block to the right-hand side. The pivot rows give the coefficients, and the
remaining transformed equations give the consistency conditions.
The generalized inverse is used in the proof specification. Gcd and translation
remain Mathlib operations. Ordinary and fraction-free RREF use the same
matrix/denominator/pivots contract.
`referenceBackend rref` supplies Mathlib factorization and resultant with the
given RREF operation. The degree bound is unchanged.
`inverseRref_mul` proves `M * U * M = M` for the prepared inverse `U`.
For a fixed rational matrix, `rationalInverseCandidate` and
`rationalInverseResidual` apply that inverse over any commutative ℚ-algebra,
without testing parameter coefficients for equality. `inverseRref_map_solve_iff`
proves exact solvability, and the candidate and residual commute with every
ℚ-algebra specialization.
`Algorithm.gosperTerm_complete` proves that any backend satisfying `Backend.Valid`
returns an output with vanishing residual exactly when a hypergeometric
antidifference exists. `Algorithm.gosperTerm_none_not_summable` certifies
nonsummability under explicit nonzero-input hypotheses when the degree bound is negative.
The algorithm returns `Option Result`; each result contains a candidate multiplier
and an array of the remaining residual equations, retained without an equality test.
When the residual vanishes, the candidate gives finite sums via
`Algorithm.gosperTerm_sum`, with explicit denominator conditions on the summation
interval. Mathlib's noncomputable
operations keep this a mathematical algorithm model.
-/
