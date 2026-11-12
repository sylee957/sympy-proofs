module

public import SympyProofs.LinearAlgebra.Permanent.Minor
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! The permanental adjugate and the trace pairing for column replacements.
The adjugate uses the transpose of the unsigned cofactor matrix. -/

@[expose] public section

namespace Matrix

variable {n : Type*}

/-- The permanental adjugate, with the same transpose convention as `Matrix.adjugate`.
Entry `(i, j)` is the permanental minor deleting row `j` and column `i`. -/
def permanentalAdjugate {R : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : Matrix n n R :=
  fun i j => permanentalMinor A j i

@[simp]
theorem permanentalAdjugate_apply {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i j : n) :
    permanentalAdjugate A i j = permanentalMinor A j i := rfl

/-- For `Fin` indices, the permanental adjugate consists of deleted-submatrix permanents. -/
theorem permanentalAdjugate_fin_apply {R : Type*} [CommSemiring R] {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) R) (i j : Fin (d + 1)) :
    permanentalAdjugate A i j = (A.submatrix j.succAbove i.succAbove).permanent :=
  permanentalMinor_fin A j i

/-- Expand the permanent along a replaced column using permanental cofactors. -/
theorem permanent_updateCol_eq_sum {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (j : n) (b : n → R) :
    (A.updateCol j b).permanent = ∑ i, permanentalAdjugate A j i * b i := by
  simp only [permanentalAdjugate_apply, permanentalMinor_eq_permanent_updateCol,
    permanent_updateCol_eq_sum_perm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Pi.single_apply, mul_comm]

/-- The column replacement sum is the trace pairing with the permanental adjugate. -/
theorem sum_permanent_updateCol_eq_trace {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A H : Matrix n n R) :
    (∑ j, (A.updateCol j (fun i => H i j)).permanent) =
      Matrix.trace (permanentalAdjugate A * H) := by
  simp only [permanent_updateCol_eq_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- Expansion along any column, with unsigned minors. -/
theorem permanent_eq_sum_column {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (j : n) :
    A.permanent = ∑ i, A i j * permanentalMinor A i j := by
  simpa [permanentalAdjugate_apply, mul_comm] using
    permanent_updateCol_eq_sum A j (fun i => A i j)

/-- Expansion along any row, with unsigned minors. -/
theorem permanent_eq_sum_row {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i : n) :
    A.permanent = ∑ j, A i j * permanentalMinor A i j := by
  simpa using permanent_eq_sum_column Aᵀ i

/-- Transposition commutes with the permanental adjugate. -/
@[simp]
theorem permanentalAdjugate_transpose {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    permanentalAdjugate Aᵀ = (permanentalAdjugate A)ᵀ := by
  ext i j
  simp [permanentalAdjugate_apply, transpose_apply]

/-- Entries of the adjugate product are permanents with a replaced column. -/
theorem permanentalAdjugate_mul_apply {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i j : n) :
    (permanentalAdjugate A * A) i j = (A.updateCol i (fun k => A k j)).permanent := by
  rw [mul_apply, permanent_updateCol_eq_sum]

/-- Entries of the reverse product are permanents with a replaced row. -/
theorem mul_permanentalAdjugate_apply {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i j : n) :
    (A * permanentalAdjugate A) i j = (A.updateRow j (fun k => A i k)).permanent := by
  have h := permanentalAdjugate_mul_apply Aᵀ j i
  simpa only [permanentalAdjugate_transpose, ← transpose_mul, transpose_apply,
    updateCol_transpose, permanent_transpose] using h

/-- Every diagonal entry of the adjugate product is the permanent. -/
@[simp]
theorem permanentalAdjugate_mul_diag {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i : n) :
    (permanentalAdjugate A * A) i i = A.permanent := by
  simp [permanentalAdjugate_mul_apply]

@[simp]
theorem mul_permanentalAdjugate_diag {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i : n) :
    (A * permanentalAdjugate A) i i = A.permanent := by
  simp [mul_permanentalAdjugate_apply]

/-- Euler's identity for the homogeneous permanent polynomial. -/
theorem trace_permanentalAdjugate_mul {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    trace (permanentalAdjugate A * A) = (Fintype.card n : R) * A.permanent := by
  simp [trace, diag, nsmul_eq_mul]

theorem trace_mul_permanentalAdjugate {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    trace (A * permanentalAdjugate A) = (Fintype.card n : R) * A.permanent := by
  simp [trace, diag, nsmul_eq_mul]

end Matrix
