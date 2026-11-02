module

public import SympyProofs.Sum.Gosper.Algorithm.Certificate
public import SympyProofs.Sum.Gosper.Backend.Inverse
public import SympyProofs.Sum.Gosper.Backend.Descent
public import SympyProofs.Sum.Gosper.Backend.Resultant
public import SympyProofs.Sum.Gosper.Normalization

/-!
# Gosper's algorithm

Normalization, coefficient descent, and polynomial solving for a rational shift
quotient `P/Q`. Results retain a candidate multiplier and residual conditions.
Soundness and completeness are proved in the accompanying modules.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Degree bound for `A(X)x(X+1) - B(X)x(X) = C(X)`, including the exceptional
integer degree from leading-term cancellation. -/
def degreeBound {K : Type*} [Field K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)] {L : Type*} [Semiring L]
    (A B : K[X]) (C : L[X]) : ℤ := Id.run do
  let l := max A.natDegree B.natDegree
  if A.coeff l ≠ B.coeff l then return (C.natDegree : ℤ) - l
  if l = 0 then return (C.natDegree : ℤ) + 1
  let ordinary := (C.natDegree : ℤ) - l + 1
  let exceptional := (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l
  if h : IsInteger ℤ exceptional then
    let k : ℤ := Encodable.choose h
    return max k ordinary
  return ordinary

/-- Convert the finitely many nonzero coefficients to a chosen smaller field.
`descendCoeff` supplies the coefficient membership test and conversion; its
correctness contract appears only in the theorems. -/
def descendPolynomial {K L : Type} [Field K] [Field L]
    (descendCoeff : L → Option K) (p : L[X]) : Option K[X] := do
  let mut q := 0
  for n in p.support.toList do
    let a ← descendCoeff (p.coeff n)
    q := q + Polynomial.monomial n a
  return q

/-- Return `(A, B, C)` with `P/Q = A(X) C(X+1) / (B(X) C(X))`.
Shift zero also removes common factors of the input pair. -/
def gosperNormal {K : Type} [Field K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (P Q : K[X]) : K[X] × K[X] × K[X] := Id.run do
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
  let mut s := (a, b, (1 : K[X]))
  for j in shifts.sort (· ≤ ·) do
    let (a, b, c) := s
    let d := gcd a (taylor (j : K) b)
    let a := a / d
    let b := taylor (-(j : K)) (taylor (j : K) b / d)
    let c := c * taylor (-1) (Gosper.shiftProduct d j)
    s := (a, b, c)
  let (a, b, c) := s
  return (Polynomial.C z * a, b, c)

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
def gosperSolve {K : Type} [Field K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)] (backend : Backend K)
    {L : Type} [CommRing L] [Algebra K L]
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

/-- The normalized polynomial that could not be represented in the chosen field. -/
inductive DescentFailure where
  | A
  | B
  deriving DecidableEq, Repr

/-- Normalize over `L`, then convert `A` and `B` to `K` and solve over `K`.
The right-hand side `C`, candidate, and residual remain over `L`.
An error identifies a failed coefficient conversion. An `ok none` instead
records the solver's negative degree bound; `ok (some r)` retains its residual.
No search for a smallest field is performed: the caller chooses `K` and supplies
`backend.descend`. For the same field, use `gosperTerm (TermBackend.self backend) P Q`.
Use `gosperSolve` directly when the normalized equation is already available.
Correctness of this conversion is required only by the proofs. -/
def gosperTerm {K : Type} [Field K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    {L : Type} [Field L] [CharZero L] [DecidableEq L]
    [DecidablePred (IsInteger ℤ : L → Prop)] [Algebra K L]
    (backend : TermBackend K L) (P Q : L[X]) : Except DescentFailure (Option (Result L)) := OptionT.run do
  let (A, B, C) := gosperNormal backend.normalization P Q
  let some A := descendPolynomial backend.descend A | throwThe DescentFailure .A
  let some B := descendPolynomial backend.descend B | throwThe DescentFailure .B
  let some result := gosperSolve backend.solver A (taylor (-1) B) C | failure
  return result

end Gosper.Algorithm
