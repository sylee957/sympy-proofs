module

public import SympyProofs.Sum.Gosper.Algorithm.Certificate
public import SympyProofs.Sum.Gosper.Backend.Inverse
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
The returned multiplier is `B*x/(d*C)`, with `d` the nonzero elimination denominator.
The residual numerator is `d*C - (A*x(X+1) - B*x)`.
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
  -- Read pivot coefficients; the residual is computed in the original polynomial equation.
  let mut coefficients := Vector.replicate n (0 : L)
  for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
    let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
    if h : pivot.val < n then
      let pivot : Fin n := ⟨pivot.val, h⟩
      coefficients := coefficients.set pivot.val transformed[row.val]
  let x := ∑ j : Fin n, Polynomial.monomial j.val coefficients[j.val]
  let U := B.map (algebraMap K L) * x
  let V := Polynomial.C (algebraMap K L r.denominator) * C
  let residual := V - (A.map (algebraMap K L) * taylor 1 x - U)
  return {
    numerator := U
    denominator := V
    residual := residual }

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
