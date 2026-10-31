module

public import SympyProofs.Sum.Gosper.Algorithm.Normalization
public import SympyProofs.Sum.Gosper.Algorithm.Degree
public import SympyProofs.Sum.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Sum.Gosper.Algorithm.Certificate
public import SympyProofs.Sum.Gosper.Backend.Inverse

/-!
# Gosper's algorithm over a characteristic-zero coefficient field

The input is P Q : K[X], the polynomial pair obtained from the forward term
ratio a(n+1)/a(n). This is the boundary after SymPy's
`parallel_poly_from_expr((p, q), n, field=True, extension=True)`.

Control flow is explicit. Arithmetic uses Mathlib polynomials for gcd, quotient,
and translation. `Backend` supplies factorization, resultant, zero matrices,
entry updates, column reads, and RREF.
Natural roots are extracted from linear factors, the shift resultant is formed
by translating a bivariate input. RREF of the coefficient matrix augmented by an
identity matrix records reusable row operations. Vector accumulation loops apply
its right block to the coefficients and give the consistency conditions.
The result retains the remaining conditions in an array for the caller to check.
Correctness of these interpretations is proved from the primitive contracts.

`referenceBackend rref` pairs Mathlib's polynomial operations and functional
matrix updates with a supplied RREF operation. Alternative implementations need
only satisfy `Backend.Valid`;
the normalization and Gosper proofs do not depend on their internal algorithms.

`DecidablePred (IsLocalization.IsInteger ℤ : K → Prop)` supplies an integer
test, and `Encodable.choose` recovers the integer witness constructively. For ℚ,
membership is decided by checking the reduced denominator. The model remains
noncomputable where Mathlib's polynomial operations are noncomputable.
`Algorithm.Correctness` proves summation soundness when the returned residual
vanishes. `Algorithm.Completeness` proves that for nonzero inputs an output with
vanishing residual exists exactly when a hypergeometric antidifference exists,
provided the backend contracts hold. Use `gosperTerm backend P Q`, or
`gosperTerm (referenceBackend rref) P Q` with reference polynomial operations.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable (backend : Backend K)

/-- A candidate multiplier together with the remaining linear compatibility conditions. -/
structure Result (K : Type*) [Field K] where
  numerator : K[X]
  denominator : K[X]
  residual : Array K

/-- Normalize, construct a candidate B*x/C, and retain its residual conditions.
Only a negative degree bound returns `none`; a nonzero residual is returned for
the caller to inspect. The candidate becomes a certificate when the residual vanishes.
Backend validity and nonzero-input hypotheses appear only in the theorems. -/
def gosperTerm (P Q : K[X]) : Option (Result K) := Id.run do
  let normal := gosperNormal backend P Q
  let B := taylor (-1) normal.B
  let d := degreeBound normal.A B normal.C
  if d < 0 then return none
  let n := d.toNat + 1
  let m := equationDegree normal.A B normal.C d.toNat + 1
  -- Augment the coefficient matrix by the identity, independently of the right-hand side.
  let mut M := backend.zeros m (n + m)
  for i in List.finRange m do
    for j in List.finRange n do
      let monomial : K[X] := X ^ (j : ℕ)
      let coeff := (normal.A * taylor 1 monomial - B * monomial).coeff i
      M := backend.setElement M i (j.castAdd m) coeff
    M := backend.setElement M i (Fin.natAdd n i) 1
  let r := backend.rref M
  let mut transformed := Vector.replicate m (0 : K)
  for i in List.finRange m do
    let mut value := (0 : K)
    for k in List.finRange m do
      value := value + r.matrix i (Fin.natAdd n k) * normal.C.coeff k
    transformed := transformed.set i.val value
  -- Read pivot coefficients; the remaining transformed equations must vanish.
  let mut coefficients := Vector.replicate n (0 : K)
  let mut residual : Array K := #[]
  for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
    let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
    if h : pivot.val < n then
      let pivot : Fin n := ⟨pivot.val, h⟩
      coefficients := coefficients.set pivot.val (transformed[row.val] / r.denominator)
    else
      residual := residual.push transformed[row.val]
  let x := Polynomial.ofFn n (fun j => coefficients[j.val])
  let U := B * x
  let V := normal.C
  return some
    { numerator := U
      denominator := V
      residual := residual }

end Gosper.Algorithm
