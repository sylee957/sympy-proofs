module

public import SympyProofs.Sum.Gosper.Algorithm.Certificate
public import SympyProofs.Sum.Gosper.Backend.Elimination
public import SympyProofs.Sum.Gosper.Backend.Normalization
public import SympyProofs.Sum.Gosper.Backend.Resultant
public import SympyProofs.Sum.Gosper.Normalization

/-!
# Gosper's algorithm

Normalization, coefficient descent, and polynomial solving for a rational shift
quotient `P/Q`. Results retain a candidate multiplier and a remainder.
Soundness and completeness are proved in the accompanying modules.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

/-- Degree bound for `A(X)x(X+1) - B(X)x(X) = C(X)`, including the exceptional
integer degree found by testing an integer ratio directly in `K`. -/
def degreeBound {K W : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CommRing W] [IsDomain W] (backend : TermBackend K W) {L : Type*} [Semiring L]
    (A B : K[X]) (C : L[X]) : ℤ := Id.run do
  let l := max A.natDegree B.natDegree
  if A.coeff l ≠ B.coeff l then return (C.natDegree : ℤ) - l
  if l = 0 then return (C.natDegree : ℤ) + 1
  let ordinary := (C.natDegree : ℤ) - l + 1
  if let some k := backend.integerRatio (B.coeff (l - 1) - A.coeff (l - 1)) (B.coeff l) then
    return max k ordinary
  return ordinary

/-- Convert the finitely many nonzero coefficients to the chosen constant domain.
`descendCoeff` supplies the coefficient membership test and conversion; its
correctness contract appears only in the theorems. -/
def descendPolynomial {K L : Type} [CommRing K] [CommRing L]
    (descendCoeff : L → Option K) (p : L[X]) : Option K[X] := do
  let mut q := 0
  for n in p.support.toList do
    let a ← descendCoeff (p.coeff n)
    q := q + Polynomial.monomial n a
  return q

/-- Return `(A, B, C)` with `P/Q = A(X) C(X+1) / (B(X) C(X))`.
All polynomials stay over `L`. Exact quotients remove the common factors;
their correctness contract appears only in the proofs. -/
def gosperNormal {K L : Type} [CommRing K] [IsDomain K] [CommRing L] [IsDomain L]
    (backend : TermBackend K L) (P Q : L[X]) : L[X] × L[X] × L[X] := Id.run do
  -- Eliminate the outer variable; the inner variable records the shift.
  let p := P.map (Polynomial.C : L →+* L[X])
  let q := taylor (X : L[X]) (Q.map (Polynomial.C : L →+* L[X]))
  let resultant := backend.resultant p q
  -- Shift zero also cancels common coefficient content.
  let shifts := insert 0 (backend.naturalRoots resultant)
  let mut s := (P, Q, (1 : L[X]))
  for j in shifts.sort (· ≤ ·) do
    let (a, b, c) := s
    let shifted := taylor (j : L) b
    let d := backend.gcd a shifted
    let a := backend.exactDiv a d
    let b := taylor (-(j : L)) (backend.exactDiv shifted d)
    let mut c := c
    for k in [:j] do
      c := c * taylor (-((k : L) + 1)) d
    s := (a, b, c)
  return s

/-- A candidate multiplier and a remainder sharing a denominator.
For an input term `t`, the residual summand is `t * residual / denominator`.
Vanishing of the residual polynomial characterizes summability. -/
structure Result (K : Type*) [CommRing K] where
  numerator : K[X]
  denominator : K[X]
  residual : K[X]

/-- Apply a coefficient homomorphism to the candidate and remainder. -/
def Result.map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : Result R) : Result S where
  numerator := r.numerator.map f
  denominator := r.denominator.map f
  residual := r.residual.map f

/-- Solve over the constant domain `K` without dividing parameter coefficients.
The returned multiplier is `B*F/(δ*C)`, with `δ` the nonzero elimination denominator.
The residual numerator is `δ*C - (A*F(X+1) - B*F)`.
The residual is returned without testing whether it vanishes in `L`.
A negative degree bound returns zero multiplier and the whole input as remainder. -/
def gosperSolve {K W : Type} [CommRing K] [IsDomain K] [DecidableEq K]
    [CommRing W] [IsDomain W] (backend : TermBackend K W)
    {L : Type} [CommRing L] [Algebra K L]
    (A B : K[X]) (C : L[X]) : Result L := Id.run do
  let d := degreeBound backend A B C
  if d < 0 then
    return {
      numerator := 0
      denominator := C
      residual := C }
  else
    let n := d.toNat + 1
    let m := max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1
    -- Each column is the image of one monomial under the polynomial equation.
    let columns : Vector K[X] n := Vector.ofFn fun j : Fin n =>
      A * taylor 1 (X ^ j.val) - B * X ^ j.val
    let mut M : Vector (Vector K n) m := Vector.ofFn fun i : Fin m =>
      Vector.ofFn fun j : Fin n => columns[j.val].coeff i.val
    let mut rhs : Vector L m := Vector.ofFn fun i : Fin m => C.coeff i.val
    let mut pivots : List (Fin n × K × Vector K n × L) := []
    -- Eliminate columns using pivots from K, retaining each pivot equation.
    for col in List.finRange n do
      let mut pivot : Option (Fin m) := none
      for i in List.finRange m do
        if M[i.val][col.val] ≠ 0 then
          pivot := some i
          break
      if let some i := pivot then
        let row := M[i.val]
        let p := row[col.val]
        let value := rhs[i.val]
        pivots := (col, p, row, value) :: pivots
        for i in List.finRange m do
          let source := M[i.val]
          let a := source[col.val]
          rhs := rhs.set i.val
            (algebraMap K L p * rhs[i.val] - algebraMap K L a * value)
          let mut updated := source
          for k in List.finRange n do
            updated := updated.set k.val (p * source[k.val] - a * row[k.val])
          M := M.set i.val updated
    -- Back-substitute in descending pivot order and reconstruct both polynomials.
    let A := A.map (algebraMap K L)
    let B := B.map (algebraMap K L)
    let mut δ := (1 : K)
    let mut F : L[X] := 0
    let mut degreeOffset := n
    let mut U : L[X] := 0
    let mut shiftedTerm : L[X] := 0
    for (degree, pivot, pivotRow, pivotRhs) in pivots do
      let mut correction := (0 : L)
      for k in List.finRange n do
        correction := correction + algebraMap K L pivotRow[k.val] * F.coeff k.val
      correction := algebraMap K L δ * pivotRhs - correction
      let pivotFactor := Polynomial.C (algebraMap K L pivot)
      F := pivotFactor * F + Polynomial.monomial degree.val correction
      δ := pivot * δ
      let gap := degreeOffset - degree.val
      let correctionTerm := Polynomial.C correction
      U := pivotFactor * X ^ gap * U + correctionTerm * B
      shiftedTerm := pivotFactor * (X + 1) ^ gap * shiftedTerm + correctionTerm * A
      degreeOffset := degree.val
    U := X ^ degreeOffset * U
    shiftedTerm := (X + 1) ^ degreeOffset * shiftedTerm
    let V := Polynomial.C (algebraMap K L δ) * C
    let R := V - (shiftedTerm - U)
    return {
      numerator := U
      denominator := V
      residual := R }

/-- The normalized polynomial that could not be represented in the constant domain. -/
inductive DescentFailure where
  | A
  | B
  deriving DecidableEq, Repr

/-- Normalize directly over `L`, descend the fixed factors `A` and `B` to `K`,
and solve with the parameter polynomial `C` over `L`.
An error identifies failed coefficient descent; every successful descent returns
a reduction. Correctness contracts appear only in the theorems. -/
def gosperTerm {K : Type} [CommRing K] [IsDomain K] [DecidableEq K]
    {L : Type} [CommRing L] [IsDomain L] [Algebra K L]
    (backend : TermBackend K L) (P Q : L[X]) : Except DescentFailure (Result L) := do
  let (A, B, C) := gosperNormal backend P Q
  let some A := descendPolynomial backend.descend A | throw .A
  let some B := descendPolynomial backend.descend B | throw .B
  return gosperSolve backend A (taylor (-1) B) C

end Gosper.Algorithm
