module

public import SympyProofs.Gosper.Degree
public import SympyProofs.Gosper.Rational

/-!
# Reduction to a finite linear system

This formalizes the concluding paragraph of the Method section. The matrix
has one column per unknown coefficient and enough rows to test polynomial
equality. The result is a mathematical reduction; it does not implement a
particular resultant, integer-root, or Gaussian-elimination algorithm.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

def equationDegree (p q r : K[X]) (N : ℕ) : ℕ :=
  max p.natDegree (max q.natDegree r.natDegree + N)

/-- Matrix of the Gosper operator on polynomials of degree at most `N`. -/
def coefficientMatrix (p q r : K[X]) (N : ℕ) :
    Matrix (Fin (equationDegree p q r N + 1)) (Fin (N + 1)) K :=
  fun i j => (operator q r (X ^ (j : ℕ))).coeff i

theorem coefficientMatrix_mulVec (p q r : K[X]) (N : ℕ) (c : Fin (N + 1) → K)
    (i : Fin (equationDegree p q r N + 1)) :
    (coefficientMatrix p q r N).mulVec c i =
      (operator q r (ofFn (N + 1) c)).coeff i := by
  rw [ofFn_eq_sum_monomial, map_sum]
  simp only [Matrix.mulVec, dotProduct, coefficientMatrix, finsetSum_coeff,
    ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq K] in
theorem operator_degree_le (q r f : K[X]) (N : ℕ) (hf : f.natDegree ≤ N) :
    (operator q r f).natDegree ≤ max q.natDegree r.natDegree + N := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by simpa using Nat.add_le_add (le_max_left _ _) hf)
  · exact natDegree_mul_le.trans (by simpa using Nat.add_le_add (le_max_right _ _) hf)

/-- Equality of the finite vectors is exactly equality of the polynomials. -/
theorem coefficientMatrix_correct (p q r : K[X]) (N : ℕ) (c : Fin (N + 1) → K) :
    (coefficientMatrix p q r N).mulVec c = toFn (equationDegree p q r N + 1) p ↔
      operator q r (ofFn (N + 1) c) = p := by
  have hf : (ofFn (N + 1) c).natDegree ≤ N :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) c)
  have ho : (operator q r (ofFn (N + 1) c)).natDegree ≤ equationDegree p q r N :=
    (operator_degree_le q r _ N hf).trans (le_max_right p.natDegree _)
  rw [ext_iff_natDegree_le ho (le_max_left _ _)]
  constructor
  · intro h i hi
    have he := congrFun h ⟨i, by omega⟩
    simpa only [coefficientMatrix_mulVec, toFn, LinearMap.pi_apply, lcoeff_apply] using he
  · intro h
    ext i
    rw [coefficientMatrix_mulVec]
    exact h i (Nat.le_of_lt_succ i.isLt)

/-- Bounded polynomial solvability is equivalent to consistency of this matrix. -/
theorem bounded_solution_iff_linearSystem (p q r : K[X]) (N : ℕ) :
    (∃ f : K[X], f.natDegree ≤ N ∧ operator q r f = p) ↔
      ∃ c, (coefficientMatrix p q r N).mulVec c = toFn (equationDegree p q r N + 1) p := by
  constructor
  · rintro ⟨f, hd, hf⟩
    refine ⟨toFn (N + 1) f, (coefficientMatrix_correct _ _ _ _ _).mpr ?_⟩
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : f.natDegree < N + 1)]
    exact hf
  · rintro ⟨c, hc⟩
    exact ⟨ofFn (N + 1) c, Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) c),
      (coefficientMatrix_correct _ _ _ _ _).mp hc⟩

/-- The finite linear-system criterion for a normalized rational solution.
Inconsistency proves nonsummability; a solution gives a polynomial certificate. -/
theorem rational_solution_iff_linearSystem [CharZero K] (p q r : K[X])
    (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r) :
    (∃ f : RatFunc K, RationalSolution p q r f) ↔
      let N := degreeBound p (taylor 1 q) r
      ∃ c, (coefficientMatrix p q r N).mulVec c = toFn (equationDegree p q r N + 1) p := by
  rw [rational_solution_iff_polynomial p q r hqr,
    ← bounded_solution_iff_linearSystem]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, solution_degree_le p (taylor 1 q) r f
      ((taylor_eq_zero _ _).not.mpr hq) hr hf, hf⟩
  · rintro ⟨f, _, hf⟩
    exact ⟨f, hf⟩

/-- The paper's criterion with its signed bound and early rejection test. -/
theorem rational_solution_iff_paperLinearSystem [CharZero K] (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r) :
    (∃ f : RatFunc K, RationalSolution p q r f) ↔
      let k := paperDegreeBound p (taylor 1 q) r
      0 ≤ k ∧ ∃ c, (coefficientMatrix p q r k.toNat).mulVec c =
        toFn (equationDegree p q r k.toNat + 1) p := by
  rw [rational_solution_iff_linearSystem p q r hq hr hqr]
  change (∃ c, (coefficientMatrix p q r (degreeBound p (taylor 1 q) r)).mulVec c =
      toFn (equationDegree p q r (degreeBound p (taylor 1 q) r) + 1) p) ↔
    0 ≤ paperDegreeBound p (taylor 1 q) r ∧ _
  constructor
  · intro h
    obtain ⟨f, _, hf⟩ :=
      (bounded_solution_iff_linearSystem p q r (degreeBound p (taylor 1 q) r)).mpr h
    exact ⟨paperDegreeBound_nonneg_of_solution p (taylor 1 q) r f hp
      ((taylor_eq_zero _ _).not.mpr hq) hr hf, h⟩
  · exact And.right

/-- Under normalization, a negative bound also excludes rational certificates. -/
theorem no_rational_solution_of_degreeBound_neg [CharZero K] (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r)
    (hk : paperDegreeBound p (taylor 1 q) r < 0) :
    ¬∃ f : RatFunc K, RationalSolution p q r f := by
  intro h
  exact (not_le_of_gt hk)
    ((rational_solution_iff_paperLinearSystem p q r hp hq hr hqr).mp h).1

end Gosper
