module

public import SympyProofs.Gosper.Backend.Resultant
public import SympyProofs.Gosper.Normalization

/-! Gosper normalization using Mathlib polynomials over a characteristic-zero field.
The algorithm takes `K : Type` so its inline loops can use ordinary `Finset ℕ` state. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]

structure NormalForm (K : Type*) [Field K] where
  A : K[X]
  B : K[X]
  C : K[X]

/-- SymPy's forward convention: P/Q = A(X) C(X+1) / (B(X) C(X)).
The loop uses Mathlib gcd, quotient, and Taylor translation. Shift zero also
removes any common factor already present in the input pair. -/
def gosperNormal (backend : Backend K) (P Q : K[X]) : NormalForm K := Id.run do
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

end Gosper.Algorithm
