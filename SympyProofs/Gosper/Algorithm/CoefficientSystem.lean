module

public import SympyProofs.Gosper.LinearSystem

/-! The forward Gosper equation as a matrix over its coefficient field. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

def forwardOperator (A B : K[X]) : K[X] →ₗ[K] K[X] where
  toFun x := A * taylor 1 x - B * x
  map_add' x y := by simp only [map_add]; ring
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_C_mul, taylor_mul, taylor_C]
    ring

omit [DecidableEq K] in
@[simp] theorem forwardOperator_apply (A B x : K[X]) :
    forwardOperator A B x = A * taylor 1 x - B * x := rfl

def equationDegree (A B C : K[X]) (d : ℕ) : ℕ :=
  max C.natDegree (max A.natDegree B.natDegree + d)

/-- Unknowns are the coefficients of x in ascending powers of X, exactly for
the equation A*x(X+1) - B*x(X) = C. The right-hand side is `toFn _ C`.
This is the proof specification for the augmented rows constructed inline in `gosperTerm`.
Unlike SymPy's `H.coeffs()`, the row range includes zero coefficient equations. -/
def coefficientSystem (A B C : K[X]) (d : ℕ) :
    Matrix (Fin (equationDegree A B C d + 1)) (Fin (d + 1)) K :=
  fun i j => (forwardOperator A B (X ^ (j : ℕ))).coeff i

theorem coefficientSystem_mulVec (A B C : K[X]) (d : ℕ) (c : Fin (d + 1) → K)
    (i : Fin (equationDegree A B C d + 1)) :
    (coefficientSystem A B C d).mulVec c i =
      (forwardOperator A B (ofFn (d + 1) c)).coeff i := by
  rw [ofFn_eq_sum_monomial, map_sum]
  simp only [Matrix.mulVec, dotProduct, coefficientSystem, finsetSum_coeff,
    ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq K] in
theorem forwardOperator_degree_le (A B x : K[X]) (d : ℕ) (hx : x.natDegree ≤ d) :
    (forwardOperator A B x).natDegree ≤ max A.natDegree B.natDegree + d := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by simpa using add_le_add (le_max_left _ _) hx)
  · exact natDegree_mul_le.trans (add_le_add (le_max_right _ _) hx)

/-- The finite matrix equation is equivalent to the full polynomial identity. -/
theorem coefficientSystem_correct (A B C : K[X]) (d : ℕ) (c : Fin (d + 1) → K) :
    (coefficientSystem A B C d).mulVec c = toFn (equationDegree A B C d + 1) C ↔
      forwardOperator A B (ofFn (d + 1) c) = C := by
  have hx : (ofFn (d + 1) c).natDegree ≤ d :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) c)
  have ho : (forwardOperator A B (ofFn (d + 1) c)).natDegree ≤ equationDegree A B C d :=
    (forwardOperator_degree_le A B _ d hx).trans (le_max_right _ _)
  rw [ext_iff_natDegree_le ho (le_max_left _ _)]
  constructor
  · intro h i hi
    have he := congrFun h ⟨i, by omega⟩
    simpa only [coefficientSystem_mulVec, toFn, LinearMap.pi_apply, lcoeff_apply] using he
  · intro h
    ext i
    rw [coefficientSystem_mulVec]
    exact h i (Nat.le_of_lt_succ i.isLt)

end Gosper.Algorithm
