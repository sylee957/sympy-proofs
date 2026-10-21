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
and translation. `Backend` supplies factorization, resultant, zero matrices,
entry updates, column reads, and RREF.
Natural roots are extracted from linear factors, the shift resultant is formed
by translating a bivariate input, and linear solutions are read from augmented
RREF. Correctness of these interpretations is proved from the primitive contracts.

`referenceBackend rref` pairs Mathlib's polynomial operations and functional
matrix updates with a supplied RREF operation. Alternative implementations need
only satisfy `Backend.Valid`;
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
  let n := d.toNat + 1
  let m := equationDegree normal.A B normal.C d.toNat + 1
  -- Rows are coefficient equations; the final column is the right-hand side.
  let mut M := backend.zeros m (n + 1)
  for i in List.finRange m do
    for j in List.finRange n do
      let monomial : K[X] := X ^ (j : ℕ)
      let coeff := (normal.A * taylor 1 monomial - B * monomial).coeff i
      M := backend.setElement M i j.castSucc coeff
    M := backend.setElement M i (Fin.last n) (normal.C.coeff i)
  let r := backend.rref M
  if Fin.last n ∈ r.pivots then return none
  let rhs := backend.getCol r.matrix (Fin.last n)
  let mut x : K[X] := 0
  for ⟨(pivot, row), h⟩ in r.pivots.zipIdx.attach do
    let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' h).1 r.length_le⟩
    x := x + Polynomial.monomial (pivot : ℕ) (rhs row / r.denominator)
  let U := B * x
  let V := normal.C
  return some ⟨U, V⟩

end Gosper.Algorithm
