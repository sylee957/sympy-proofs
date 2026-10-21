module

public import SympyProofs.Gosper.Algorithm.Polynomial
public import SympyProofs.Gosper.Normalization

/-! Gosper normalization using Mathlib polynomial operations over a field. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K]

local instance normalizationDecidableEq : DecidableEq K := Classical.decEq K

/-- Res_X(p(X), q(X+h)), as a polynomial in h. In `K[X][X]` the inner
variable is h and the outer variable is X. Mathlib computes the resultant. -/
def shiftResultant (p q : K[X]) : K[X] :=
  Polynomial.resultant (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))
    p.natDegree q.natDegree

theorem shiftResultant_eval (p q : K[X]) (a : K) :
    (shiftResultant p q).eval a =
      Polynomial.resultant p (taylor a q) p.natDegree q.natDegree := by
  have hc : (Polynomial.evalRingHom a).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
    ext c
    exact Polynomial.eval_C
  have h := Polynomial.resultant_map_map
    (p.map (Polynomial.C : K →+* K[X]))
    (taylor (X : K[X]) (q.map (Polynomial.C : K →+* K[X])))
    p.natDegree q.natDegree (Polynomial.evalRingHom a)
  change (Polynomial.evalRingHom a) _ = _
  unfold shiftResultant
  rw [← h]
  congr 1 <;> simp [Polynomial.map_map, hc]

/-- Filter the field roots to the nonnegative integers and sort them. For
nonzero input this lists exactly the shifts relevant to normalization. -/
def nonnegativeIntegerRoots (p : K[X]) : List ℕ :=
  (p.roots.toFinset.toList.filterMap naturalValue).mergeSort (· ≤ ·)

theorem mem_nonnegativeIntegerRoots [CharZero K] (p : K[X]) (hp : p ≠ 0) (n : ℕ) :
    n ∈ nonnegativeIntegerRoots p ↔ p.eval (n : K) = 0 := by
  simp only [nonnegativeIntegerRoots, List.mem_mergeSort, List.mem_filterMap,
    Finset.mem_toList, Multiset.mem_toFinset, naturalValue_eq_some]
  constructor
  · rintro ⟨a, ha, he⟩
    subst a
    exact (Polynomial.mem_roots hp).mp ha
  · intro h
    exact ⟨n, (Polynomial.mem_roots hp).mpr h, rfl⟩

/-- The detected shifts are precisely those for which the two translated
polynomials have a nonconstant common factor, as in the paper. -/
theorem mem_normalization_shifts [CharZero K] (p q : K[X]) (hp : p ≠ 0)
    (hR : shiftResultant p q ≠ 0) (j : ℕ) :
    j ∈ nonnegativeIntegerRoots (shiftResultant p q) ↔
      ¬ IsCoprime p (taylor (j : K) q) := by
  rw [mem_nonnegativeIntegerRoots _ hR, shiftResultant_eval]
  simpa [hp] using (Polynomial.resultant_eq_zero_iff (f := p) (g := taylor (j : K) q))

structure NormalForm (K : Type*) [Field K] where
  A : K[X]
  B : K[X]
  C : K[X]
  shifts : List ℕ

/-- SymPy's forward convention: P/Q = A(X) C(X+1) / (B(X) C(X)).
The loop uses Mathlib gcd, quotient, and Taylor translation. Shift zero also
removes any common factor already present in the input pair. -/
def gosperNormal (P Q : K[X]) : NormalForm K := Id.run do
  let z := P.leadingCoeff / Q.leadingCoeff
  let a := monic P
  let b := monic Q
  let resultant := shiftResultant a b
  let roots := nonnegativeIntegerRoots resultant
  let mut s : NormalForm K := ⟨a, b, 1, roots⟩
  for j in roots do
    let d := gcd s.A (taylor (j : K) s.B)
    let a := s.A / d
    let b := taylor (-(j : K)) (taylor (j : K) s.B / d)
    let c := s.C * taylor (-1) (Gosper.shiftProduct d j)
    s := ⟨a, b, c, s.shifts⟩
  return ⟨Polynomial.C z * s.A, s.B, s.C, roots⟩

end Gosper.Algorithm
