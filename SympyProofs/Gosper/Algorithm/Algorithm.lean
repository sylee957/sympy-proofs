module

public import SympyProofs.Gosper.Algorithm.Normalization
public import SympyProofs.Gosper.Algorithm.Degree
public import SympyProofs.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Gosper.Algorithm.Certificate

/-!
# Gosper's algorithm over a characteristic-zero coefficient field

The input is P Q : K[X], the polynomial pair obtained from the forward term
ratio a(n+1)/a(n). This is the boundary after SymPy's
`parallel_poly_from_expr((p, q), n, field=True, extension=True)`.

Control flow is explicit. Arithmetic uses Mathlib polynomials for gcd, quotient,
and translation. `Backend` supplies exactly factorization, resultant, and RREF.
Natural roots are extracted from linear factors, the shift resultant is formed
by translating a bivariate input, and linear solutions are read from augmented
RREF. Correctness of these interpretations is proved from the primitive contracts.

`referenceBackend rref` pairs Mathlib's factorization and resultant with a supplied
RREF operation. Alternative implementations need only satisfy `Backend.Valid`;
the normalization and Gosper proofs do not depend on their internal algorithms.

`DecidablePred (IsLocalization.IsInteger ℤ : K → Prop)` supplies an integer
test, and `Encodable.choose` recovers the integer witness constructively. For ℚ,
membership is decided by checking the reduced denominator. The model remains
noncomputable where Mathlib's polynomial operations are noncomputable.
`Algorithm.Correctness` proves summation
soundness, and `Algorithm.Completeness` proves that for nonzero inputs the
procedure succeeds exactly when a hypergeometric antidifference exists, provided
the backend contracts hold. Use `gosperTerm backend P Q`, or
`gosperTerm (referenceBackend rref) P Q` with reference polynomial operations.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable (backend : Backend K)

structure Certificate (K : Type*) [Field K] where
  numerator : K[X]
  denominator : K[X]

/-- Normalize, solve the bounded polynomial equation, and return B*x/C
without reducing the final fraction. A negative degree bound or a pivot in the
right-hand-side column returns `none`.
The soundness and completeness proofs use `backend.Valid` to establish the
returned identity and complete shift detection without runtime checks.
Nonzero-input hypotheses are stated in the theorems. -/
def gosperTerm (P Q : K[X]) : Option (Certificate K) := Id.run do
  let normal := gosperNormal backend P Q
  let B := taylor (-1) normal.B
  let d := degreeBound normal.A B normal.C
  if d < 0 then return none
  let M := coefficientSystem normal.A B normal.C d.toNat
  let b := toFn (equationDegree normal.A B normal.C d.toNat + 1) normal.C
  let r := backend.rref (augmented M b)
  if Fin.last (d.toNat + 1) ∈ r.pivots then return none
  let x := ofFn (d.toNat + 1) r.solution
  let U := B * x
  let V := normal.C
  return some ⟨U, V⟩

end Gosper.Algorithm
