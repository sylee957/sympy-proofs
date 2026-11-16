module

public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic

/-!
# The rotation matrix of a unit quaternion

`toRotationMatrix q` is the rotation matrix of a unit quaternion
`q = a + b i + c j + d k`, written out in its components.

For `M = toRotationMatrix q` with `q` a unit quaternion, all ten products `4 qᵢ qⱼ` are
linear in the entries of `M`:

* `4a² = 1 + M₀₀ + M₁₁ + M₂₂`, `4b² = 1 + M₀₀ - M₁₁ - M₂₂`,
  `4c² = 1 - M₀₀ + M₁₁ - M₂₂`, `4d² = 1 - M₀₀ - M₁₁ + M₂₂`;
* `4ab = M₂₁ - M₁₂`, `4ac = M₀₂ - M₂₀`, `4ad = M₁₀ - M₀₁`;
* `4bc = M₀₁ + M₁₀`, `4bd = M₀₂ + M₂₀`, `4cd = M₁₂ + M₂₁`.

Conversely, `toRotationMatrix_eq_of_products` recovers `toRotationMatrix q = M` and
`normSq q = 1` from these ten equations. The polynomial relations among the entries of a
matrix in `SO(3)` needed to verify them are collected in `RotationRelations`.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-- The rotation matrix of a unit quaternion. -/
def toRotationMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := q.re
  let b := q.imI
  let c := q.imJ
  let d := q.imK
  -- The diagonal entries.
  let m00 := 1 - 2 * (c ^ 2 + d ^ 2)
  let m11 := 1 - 2 * (b ^ 2 + d ^ 2)
  let m22 := 1 - 2 * (b ^ 2 + c ^ 2)
  -- The off-diagonal entries.
  let m01 := 2 * (b * c - d * a)
  let m02 := 2 * (b * d + c * a)
  let m10 := 2 * (b * c + d * a)
  let m12 := 2 * (c * d - b * a)
  let m20 := 2 * (b * d - c * a)
  let m21 := 2 * (c * d + b * a)
  !![m00, m01, m02;
    m10, m11, m12;
    m20, m21, m22]

/-- The polynomial relations satisfied by the entries of a matrix in `SO(3)`: rows and
columns are orthonormal, and every entry equals its own cofactor. -/
structure RotationRelations (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  r00 : M 0 0 * M 0 0 + M 0 1 * M 0 1 + M 0 2 * M 0 2 = 1
  r01 : M 0 0 * M 1 0 + M 0 1 * M 1 1 + M 0 2 * M 1 2 = 0
  r02 : M 0 0 * M 2 0 + M 0 1 * M 2 1 + M 0 2 * M 2 2 = 0
  r11 : M 1 0 * M 1 0 + M 1 1 * M 1 1 + M 1 2 * M 1 2 = 1
  r12 : M 1 0 * M 2 0 + M 1 1 * M 2 1 + M 1 2 * M 2 2 = 0
  r22 : M 2 0 * M 2 0 + M 2 1 * M 2 1 + M 2 2 * M 2 2 = 1
  c00 : M 0 0 * M 0 0 + M 1 0 * M 1 0 + M 2 0 * M 2 0 = 1
  c01 : M 0 0 * M 0 1 + M 1 0 * M 1 1 + M 2 0 * M 2 1 = 0
  c02 : M 0 0 * M 0 2 + M 1 0 * M 1 2 + M 2 0 * M 2 2 = 0
  c11 : M 0 1 * M 0 1 + M 1 1 * M 1 1 + M 2 1 * M 2 1 = 1
  c12 : M 0 1 * M 0 2 + M 1 1 * M 1 2 + M 2 1 * M 2 2 = 0
  c22 : M 0 2 * M 0 2 + M 1 2 * M 1 2 + M 2 2 * M 2 2 = 1
  k00 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = M 0 0
  k01 : M 1 2 * M 2 0 - M 1 0 * M 2 2 = M 0 1
  k02 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = M 0 2
  k10 : M 0 2 * M 2 1 - M 0 1 * M 2 2 = M 1 0
  k11 : M 0 0 * M 2 2 - M 0 2 * M 2 0 = M 1 1
  k12 : M 0 1 * M 2 0 - M 0 0 * M 2 1 = M 1 2
  k20 : M 0 1 * M 1 2 - M 0 2 * M 1 1 = M 2 0
  k21 : M 0 2 * M 1 0 - M 0 0 * M 1 2 = M 2 1
  k22 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = M 2 2

/-- A matrix in `SO(3)` is its own cofactor matrix. -/
theorem adjugate_eq_transpose_of_mem_specialOrthogonalGroup {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : M.adjugate = Mᵀ := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hM
  have h : M * Mᵀ = 1 := (mem_orthogonalGroup_iff (A := M)).1 hO
  calc M.adjugate = M.adjugate * (M * Mᵀ) := by rw [h, Matrix.mul_one]
    _ = Mᵀ := by rw [← Matrix.mul_assoc, adjugate_mul, hdet, one_smul, Matrix.one_mul]

/-- The entrywise relations of a matrix in `SO(3)`. -/
theorem rotationRelations_of_mem_specialOrthogonalGroup {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : RotationRelations M := by
  have hO := (mem_specialOrthogonalGroup_iff.mp hM).1
  have h1 : M * Mᵀ = 1 := (mem_orthogonalGroup_iff (A := M)).1 hO
  have h2 : Mᵀ * M = 1 := (mem_orthogonalGroup_iff' (A := M)).1 hO
  have h3 := adjugate_eq_transpose_of_mem_specialOrthogonalGroup hM
  have e1 := fun i j => congrFun (congrFun h1 i) j
  have e2 := fun i j => congrFun (congrFun h2 i) j
  have e3 := fun i j => congrFun (congrFun h3 i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at e1 e2
  rw [adjugate_fin_three] at e3
  have r00 := e1 0 0; have r01 := e1 0 1; have r02 := e1 0 2
  have r11 := e1 1 1; have r12 := e1 1 2; have r22 := e1 2 2
  have c00 := e2 0 0; have c01 := e2 0 1; have c02 := e2 0 2
  have c11 := e2 1 1; have c12 := e2 1 2; have c22 := e2 2 2
  have k00 := e3 0 0; have k01 := e3 1 0; have k02 := e3 2 0
  have k10 := e3 0 1; have k11 := e3 1 1; have k12 := e3 2 1
  have k20 := e3 0 2; have k21 := e3 1 2; have k22 := e3 2 2
  simp at r00 r01 r02 r11 r12 r22 c00 c01 c02 c11 c12 c22
  simp at k00 k01 k02 k10 k11 k12 k20 k21 k22
  constructor <;> linarith

/-- A quaternion whose ten products `4 qᵢ qⱼ` take the values prescribed by `M` is a unit
quaternion with rotation matrix `M`. -/
theorem toRotationMatrix_eq_of_products {M : Matrix (Fin 3) (Fin 3) ℝ} {q : ℍ[ℝ]}
    (h00 : 4 * (q.re * q.re) = 1 + M 0 0 + M 1 1 + M 2 2)
    (h11 : 4 * (q.imI * q.imI) = 1 + M 0 0 - M 1 1 - M 2 2)
    (h22 : 4 * (q.imJ * q.imJ) = 1 - M 0 0 + M 1 1 - M 2 2)
    (h33 : 4 * (q.imK * q.imK) = 1 - M 0 0 - M 1 1 + M 2 2)
    (h01 : 4 * (q.re * q.imI) = M 2 1 - M 1 2)
    (h02 : 4 * (q.re * q.imJ) = M 0 2 - M 2 0)
    (h03 : 4 * (q.re * q.imK) = M 1 0 - M 0 1)
    (h12 : 4 * (q.imI * q.imJ) = M 0 1 + M 1 0)
    (h13 : 4 * (q.imI * q.imK) = M 0 2 + M 2 0)
    (h23 : 4 * (q.imJ * q.imK) = M 1 2 + M 2 1) :
    toRotationMatrix q = M ∧ normSq q = 1 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [toRotationMatrix] <;> nlinarith
  · rw [normSq_def']
    nlinarith

end SympyQuaternion
