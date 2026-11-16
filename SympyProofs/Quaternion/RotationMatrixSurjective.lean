module

public import SympyProofs.Quaternion.ToRotationMatrix
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Every rotation matrix is the rotation matrix of a unit quaternion

`exists_toRotationMatrix_eq`: for `M ∈ SO(3)` there is a unit quaternion `q` with
`toRotationMatrix q = M`.

The four squares `4a²`, `4b²`, `4c²`, `4d²` determined by `M` sum to `4`, so one of them
is positive. The proof takes the first positive one as a pivot and divides the
corresponding column of the symmetric matrix `4 q qᵀ` by twice the square root of the
pivot. This construction is used only for existence; the conversion formula of this
directory is `fromScaledRotationMatrix`.

A consequence is `neg_one_le_trace_of_mem_specialOrthogonalGroup`: the trace of a rotation
matrix is at least `-1`.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

private theorem four_mul_div_mul_div {s x y z : ℝ} (hs : s ≠ 0) (h : x * y = s ^ 2 * z) :
    4 * (x / (2 * s) * (y / (2 * s))) = z := by
  field_simp
  linear_combination 4 * h

/-- The first positive entry among `4a²`, `4b²`, `4c²`, `4d²` is the pivot `t`, and the
result is the corresponding column of `4 q qᵀ` divided by `2 √t`. -/
private noncomputable def pivotQuaternion (M : Matrix (Fin 3) (Fin 3) ℝ) : ℍ[ℝ] :=
  let t0 := 1 + M 0 0 + M 1 1 + M 2 2
  let t1 := 1 + M 0 0 - M 1 1 - M 2 2
  let t2 := 1 - M 0 0 + M 1 1 - M 2 2
  let t3 := 1 - M 0 0 - M 1 1 + M 2 2
  if 0 < t0 then
    ⟨t0 / (2 * √t0), (M 2 1 - M 1 2) / (2 * √t0), (M 0 2 - M 2 0) / (2 * √t0),
      (M 1 0 - M 0 1) / (2 * √t0)⟩
  else if 0 < t1 then
    ⟨(M 2 1 - M 1 2) / (2 * √t1), t1 / (2 * √t1), (M 0 1 + M 1 0) / (2 * √t1),
      (M 0 2 + M 2 0) / (2 * √t1)⟩
  else if 0 < t2 then
    ⟨(M 0 2 - M 2 0) / (2 * √t2), (M 0 1 + M 1 0) / (2 * √t2), t2 / (2 * √t2),
      (M 1 2 + M 2 1) / (2 * √t2)⟩
  else
    ⟨(M 1 0 - M 0 1) / (2 * √t3), (M 0 2 + M 2 0) / (2 * √t3), (M 1 2 + M 2 1) / (2 * √t3),
      t3 / (2 * √t3)⟩

private theorem pivotQuaternion_spec {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    toRotationMatrix (pivotQuaternion M) = M ∧ normSq (pivotQuaternion M) = 1 := by
  have F := rotationRelations_of_mem_specialOrthogonalGroup hM
  unfold pivotQuaternion
  extract_lets t0 t1 t2 t3
  have key : ∀ t : ℝ, 0 < t → √t ≠ 0 ∧ √t ^ 2 = t := fun t ht =>
    ⟨(Real.sqrt_pos.2 ht).ne', Real.sq_sqrt ht.le⟩
  split_ifs with h0 h1 h2
  · obtain ⟨hs, hsq⟩ := key t0 h0
    apply toRotationMatrix_eq_of_products <;> refine four_mul_div_mul_div hs ?_ <;>
      rw [hsq] <;>
      linarith [F.r00, F.r01, F.r02, F.r11, F.r12, F.r22, F.c00, F.c01, F.c02, F.c11, F.c12,
        F.c22, F.k00, F.k01, F.k02, F.k10, F.k11, F.k12, F.k20, F.k21, F.k22]
  · obtain ⟨hs, hsq⟩ := key t1 h1
    apply toRotationMatrix_eq_of_products <;> refine four_mul_div_mul_div hs ?_ <;>
      rw [hsq] <;>
      linarith [F.r00, F.r01, F.r02, F.r11, F.r12, F.r22, F.c00, F.c01, F.c02, F.c11, F.c12,
        F.c22, F.k00, F.k01, F.k02, F.k10, F.k11, F.k12, F.k20, F.k21, F.k22]
  · obtain ⟨hs, hsq⟩ := key t2 h2
    apply toRotationMatrix_eq_of_products <;> refine four_mul_div_mul_div hs ?_ <;>
      rw [hsq] <;>
      linarith [F.r00, F.r01, F.r02, F.r11, F.r12, F.r22, F.c00, F.c01, F.c02, F.c11, F.c12,
        F.c22, F.k00, F.k01, F.k02, F.k10, F.k11, F.k12, F.k20, F.k21, F.k22]
  · have h3 : 0 < t3 := by simp only [t0, t1, t2, t3] at *; linarith
    obtain ⟨hs, hsq⟩ := key t3 h3
    apply toRotationMatrix_eq_of_products <;> refine four_mul_div_mul_div hs ?_ <;>
      rw [hsq] <;>
      linarith [F.r00, F.r01, F.r02, F.r11, F.r12, F.r22, F.c00, F.c01, F.c02, F.c11, F.c12,
        F.c22, F.k00, F.k01, F.k02, F.k10, F.k11, F.k12, F.k20, F.k21, F.k22]

/-- Every rotation matrix is the rotation matrix of a unit quaternion. -/
theorem exists_toRotationMatrix_eq {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ q : ℍ[ℝ], normSq q = 1 ∧ toRotationMatrix q = M :=
  ⟨pivotQuaternion M, (pivotQuaternion_spec hM).2, (pivotQuaternion_spec hM).1⟩

/-- A matrix in `SO(3)` has trace at least `-1`. -/
theorem neg_one_le_trace_of_mem_specialOrthogonalGroup {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : -1 ≤ M.trace := by
  obtain ⟨q, h2, rfl⟩ := exists_toRotationMatrix_eq hM
  rw [normSq_def'] at h2
  rw [Matrix.trace_fin_three]
  simp only [toRotationMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  nlinarith [sq_nonneg q.re]

end SympyQuaternion
