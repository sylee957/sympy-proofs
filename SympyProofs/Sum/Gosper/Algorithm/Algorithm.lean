module

public import SympyProofs.Sum.Gosper.Algorithm.Certificate
public import SympyProofs.Sum.Gosper.Backend.Inverse
public import SympyProofs.Sum.Gosper.Backend.Resultant
public import SympyProofs.Sum.Gosper.Normalization

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
`B`; `C` and the result may lie in a commutative `K`-algebra. The degree of `C`
determines the matrix dimensions. The retained output specializes correctly
even when evaluation lowers that degree. Use `gosperTerm backend P Q`, or
`gosperTerm (referenceBackend rref) P Q` with reference polynomial operations.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

section DegreeBounds

variable {K : Type*} [Field K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- Bound for A(X)x(X+1) - B(X)x(X) = C(X). Testing coefficients at the
maximum degree combines SymPy's unequal-degree / unequal-leading-term cases.
The exceptional integer root is retained even when negative. -/
def degreeBound {L : Type*} [Semiring L] (A B : K[X]) (C : L[X]) : ℤ := Id.run do
  let l := max A.natDegree B.natDegree
  if A.coeff l ≠ B.coeff l then return (C.natDegree : ℤ) - l
  if l = 0 then return (C.natDegree : ℤ) + 1
  let ordinary := (C.natDegree : ℤ) - l + 1
  let exceptional := (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l
  if h : IsInteger ℤ exceptional then
    let k : ℤ := Encodable.choose h
    return max k ordinary
  return ordinary

end DegreeBounds

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable (backend : Backend K)

structure NormalForm (K : Type*) [Field K] where
  A : K[X]
  B : K[X]
  C : K[X]

/-- SymPy's forward convention: P/Q = A(X) C(X+1) / (B(X) C(X)).
The loop uses Mathlib gcd, quotient, and Taylor translation. Shift zero also
removes any common factor already present in the input pair. -/
def gosperNormal (P Q : K[X]) : NormalForm K := Id.run do
  let z := P.leadingCoeff / Q.leadingCoeff
  let a := monic P
  let b := monic Q
  let mappedA := a.map (Polynomial.C : K →+* K[X])
  let shiftedB := taylor (X : K[X]) (b.map (Polynomial.C : K →+* K[X]))
  let resultant := backend.resultant mappedA shiftedB
  let (_, factors) := backend.factor resultant
  let mut shifts : Finset ℕ := ∅
  for (base, _) in factors do
    if base.natDegree = 1 then
      let root := -base.coeff 0 / base.coeff 1
      if h : IsInteger ℤ root then
        let n : ℤ := Encodable.choose h
        if 0 ≤ n then
          shifts := insert n.toNat shifts
  let mut s : NormalForm K := ⟨a, b, 1⟩
  for j in shifts.sort (· ≤ ·) do
    let d := gcd s.A (taylor (j : K) s.B)
    let a := s.A / d
    let b := taylor (-(j : K)) (taylor (j : K) s.B / d)
    let c := s.C * taylor (-1) (Gosper.shiftProduct d j)
    s := ⟨a, b, c⟩
  return ⟨Polynomial.C z * s.A, s.B, s.C⟩

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
The matrix entries depend on `A` and `B`; its size uses `C.natDegree`.
The retained candidate and residual can be specialized even when this degree drops.
Only a negative degree bound returns `none`; a nonzero residual is returned for
the caller to inspect. The field-valued rational multiplier interpretation
requires `C ≠ 0` after specialization.
Backend validity and nonzero-input hypotheses appear only in the theorems. -/
def gosperSolve {L : Type} [CommRing L] [Algebra K L]
    (A B : K[X]) (C : L[X]) : Option (Result L) := Id.run do
  let d := degreeBound A B C
  if d < 0 then return none
  let n := d.toNat + 1
  let m := max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1
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
