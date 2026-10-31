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
provided the backend contracts hold. `gosperSolve backend A B C` takes the
normalized forward equation directly. Its matrix is over the field of `A` and
`B`; `C` and the result may lie in a commutative `K`-algebra. Supply the same
degree bound `N` before and after specializing parameters to keep the matrix
dimensions fixed. Use `gosperTerm backend P Q`, or
`gosperTerm (referenceBackend rref) P Q` with reference polynomial operations.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable (backend : Backend K)

/-- A candidate multiplier together with the remaining linear compatibility conditions. -/
structure Result (K : Type*) [CommRing K] where
  numerator : K[X]
  denominator : K[X]
  residual : Array K

/-- Solve the normalized equation `A*x(X+1) - B*x = C`, retaining a candidate
`B*x/C` and its residual conditions. Here `B` is already shifted backward from
the `B` returned by `gosperNormal`. Matrix reduction takes place over `K`;
the right-hand side and result lie in a commutative `K`-algebra `L`.
No decidable equality on `L` is required; residual conditions are returned
without deciding whether they vanish.
The matrix entries depend on `A` and `B`; its size uses the supplied degree
bound `N`. Omission of `N` uses `C.natDegree`. Correctness with an explicit
bound assumes `C.natDegree ≤ N`, only in the theorems.
Only a negative degree bound returns `none`; a nonzero residual is returned for
the caller to inspect. The field-valued rational multiplier interpretation
requires `C ≠ 0` after specialization.
Backend validity and nonzero-input hypotheses appear only in the theorems. -/
def gosperSolve {L : Type} [CommRing L] [Algebra K L]
    (A B : K[X]) (C : L[X]) (N : ℕ := C.natDegree) : Option (Result L) := Id.run do
  let d := degreeBound A B C N
  if d < 0 then return none
  let n := d.toNat + 1
  let m := equationDegree A B C d.toNat N + 1
  -- Augment the coefficient matrix by the identity, independently of the right-hand side.
  let mut M := backend.zeros m (n + m)
  for i in List.finRange m do
    for j in List.finRange n do
      let monomial : K[X] := X ^ (j : ℕ)
      let coeff := (A * taylor 1 monomial - B * monomial).coeff i
      M := backend.setElement M i (j.castAdd m) coeff
    M := backend.setElement M i (Fin.natAdd n i) 1
  let r := backend.rref M
  let mut transformed := Vector.replicate m (0 : L)
  for i in List.finRange m do
    let mut value := (0 : L)
    for k in List.finRange m do
      value := value + algebraMap K L (r.matrix i (Fin.natAdd n k)) * C.coeff k
    transformed := transformed.set i.val value
  -- Read pivot coefficients; the remaining transformed equations must vanish.
  let mut coefficients := Vector.replicate n (0 : L)
  let mut residual : Array L := #[]
  for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
    let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
    if h : pivot.val < n then
      let pivot : Fin n := ⟨pivot.val, h⟩
      coefficients := coefficients.set pivot.val
        (transformed[row.val] * algebraMap K L r.denominator⁻¹)
    else
      residual := residual.push transformed[row.val]
  let x := ∑ j : Fin n, Polynomial.monomial j.val coefficients[j.val]
  let U := B.map (algebraMap K L) * x
  let V := C
  return some
    { numerator := U
      denominator := V
      residual := residual }

/-- Normalize the forward ratio `P/Q`, then solve its polynomial equation.
Use `gosperSolve` directly when `A`, `B`, and `C` are already available. -/
def gosperTerm (P Q : K[X]) : Option (Result K) :=
  let normal := gosperNormal backend P Q
  gosperSolve backend normal.A (taylor (-1) normal.B) normal.C

end Gosper.Algorithm
