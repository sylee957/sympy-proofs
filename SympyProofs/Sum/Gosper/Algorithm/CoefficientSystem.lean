module

public import SympyProofs.Sum.Gosper.LinearSystem

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

def equationDegree {L : Type*} [Semiring L] (A B : K[X]) (C : L[X]) (d : ℕ)
    (N : ℕ := C.natDegree) : ℕ :=
  max N (max A.natDegree B.natDegree + d)

omit [DecidableEq K] in
theorem equationDegree_rhs_eq {R S : Type*} [Semiring R] [Semiring S]
    (A B : K[X]) (C : R[X]) (D : S[X]) (d N : ℕ) :
    equationDegree A B C d N = equationDegree A B D d N := rfl

/-- Unknowns are the coefficients of x in ascending powers of X, exactly for
the equation A*x(X+1) - B*x(X) = C. The right-hand side is `toFn _ C`.
This is the proof specification for the coefficient rows constructed inline in `gosperTerm`.
Unlike SymPy's `H.coeffs()`, the row range includes zero coefficient equations. -/
def coefficientSystem {L : Type*} [Semiring L] (A B : K[X]) (C : L[X]) (d : ℕ)
    (N : ℕ := C.natDegree) :
    Matrix (Fin (equationDegree A B C d N + 1)) (Fin (d + 1)) K :=
  fun i j => (forwardOperator A B (X ^ (j : ℕ))).coeff i

omit [DecidableEq K] in
/-- Fixing both degree bounds makes the matrix independent of the right-hand side. -/
theorem coefficientSystem_rhs_eq {R S : Type*} [Semiring R] [Semiring S]
    (A B : K[X]) (C : R[X]) (D : S[X]) (d N : ℕ) :
    coefficientSystem A B C d N = coefficientSystem A B D d N := rfl

theorem coefficientSystem_mulVec_bounded {L : Type*} [Semiring L]
    (A B : K[X]) (C : L[X]) (d N : ℕ) (c : Fin (d + 1) → K)
    (i : Fin (equationDegree A B C d N + 1)) :
    (coefficientSystem A B C d N).mulVec c i =
      (forwardOperator A B (ofFn (d + 1) c)).coeff i := by
  rw [ofFn_eq_sum_monomial, map_sum]
  simp only [Matrix.mulVec, dotProduct, coefficientSystem, finsetSum_coeff,
    ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coefficientSystem_mulVec {L : Type*} [Semiring L]
    (A B : K[X]) (C : L[X]) (d : ℕ) (c : Fin (d + 1) → K)
    (i : Fin (equationDegree A B C d + 1)) :
    (coefficientSystem A B C d).mulVec c i =
      (forwardOperator A B (ofFn (d + 1) c)).coeff i :=
  coefficientSystem_mulVec_bounded A B C d C.natDegree c i

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

section Extension

variable {L : Type*} [Field L] [Algebra K L] [DecidableEq L]

omit [DecidableEq K] in
/-- The coefficient rows stay over `K` when the unknown coefficients lie in `L`. -/
theorem coefficientSystem_mulVec_extension_bounded (A B : K[X]) (C : L[X])
    (d N : ℕ) (c : Fin (d + 1) → L) (i : Fin (equationDegree A B C d N + 1)) :
    ((coefficientSystem A B C d N).map (algebraMap K L)).mulVec c i =
      (forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
        (ofFn (d + 1) c)).coeff i := by
  have hentry (j : ℕ) :
      algebraMap K L ((forwardOperator A B (X ^ j)).coeff i) =
        (forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
          (X ^ j)).coeff i := by
    simp [← coeff_map, forwardOperator_apply]
  rw [ofFn_eq_sum_monomial, map_sum]
  simp only [Matrix.mulVec, dotProduct, coefficientSystem, Matrix.map_apply,
    finsetSum_coeff, ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul,
    coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hentry]
  ring

omit [DecidableEq K] in
theorem coefficientSystem_mulVec_extension (A B : K[X]) (C : L[X])
    (d : ℕ) (c : Fin (d + 1) → L) (i : Fin (equationDegree A B C d + 1)) :
    ((coefficientSystem A B C d).map (algebraMap K L)).mulVec c i =
      (forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
        (ofFn (d + 1) c)).coeff i :=
  coefficientSystem_mulVec_extension_bounded A B C d C.natDegree c i

omit [DecidableEq K] in
/-- The matrix built over `K` represents the polynomial equation over its extension `L`. -/
theorem coefficientSystem_correct_extension_bounded (A B : K[X]) (C : L[X])
    (d N : ℕ) (hC : C.natDegree ≤ N) (c : Fin (d + 1) → L) :
    ((coefficientSystem A B C d N).map (algebraMap K L)).mulVec c =
        toFn (equationDegree A B C d N + 1) C ↔
      forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
        (ofFn (d + 1) c) = C := by
  have hx : (ofFn (d + 1) c).natDegree ≤ d :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) c)
  have ho :
      (forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
        (ofFn (d + 1) c)).natDegree ≤ equationDegree A B C d N := by
    apply (forwardOperator_degree_le _ _ _ d hx).trans
    simpa only [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
      equationDegree] using le_max_right N (max A.natDegree B.natDegree + d)
  rw [ext_iff_natDegree_le ho (hC.trans (le_max_left _ _))]
  constructor
  · intro h i hi
    have he := congrFun h ⟨i, by omega⟩
    simpa only [coefficientSystem_mulVec_extension_bounded, toFn, LinearMap.pi_apply, lcoeff_apply]
      using he
  · intro h
    ext i
    rw [coefficientSystem_mulVec_extension_bounded]
    exact h i (Nat.le_of_lt_succ i.isLt)

omit [DecidableEq K] in
theorem coefficientSystem_correct_extension (A B : K[X]) (C : L[X])
    (d : ℕ) (c : Fin (d + 1) → L) :
    ((coefficientSystem A B C d).map (algebraMap K L)).mulVec c =
        toFn (equationDegree A B C d + 1) C ↔
      forwardOperator (A.map (algebraMap K L)) (B.map (algebraMap K L))
        (ofFn (d + 1) c) = C :=
  coefficientSystem_correct_extension_bounded A B C d C.natDegree le_rfl c

end Extension

end Gosper.Algorithm
