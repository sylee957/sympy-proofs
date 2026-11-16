module

public import SympyProofs.Quaternion.ToRotationMatrix
public import SympyProofs.Quaternion.RepresentsRotation

/-!
# The rotation matrix as the conjugation action of a unit quaternion

A unit quaternion `q` acts on pure quaternions by `v ↦ q v q⁻¹ = q v q*`.
`toRotationMatrix q` is the matrix of this action, which connects the explicit formula to
the specification `RepresentsRotation`:

* `mul_ofVector_mul_star`: `q * ofVector v * star q = ofVector (toRotationMatrix q *ᵥ v)`;
* `representsRotation_iff`: `RepresentsRotation q M ↔ normSq q = 1 ∧ toRotationMatrix q = M`,
  so the matrix represented by a unit quaternion is `toRotationMatrix q` and nothing else;
* `toRotationMatrix_mem_specialOrthogonalGroup`: the matrix is a rotation;
* `toRotationMatrix_mul`: products of unit quaternions go to products of matrices;
* `toRotationMatrix_eq_iff`: two unit quaternions give the same rotation exactly when
  they are equal up to sign.

So `toRotationMatrix` is the two-to-one homomorphism from unit quaternions onto `SO(3)`,
and a quaternion "from a rotation matrix" is a choice of one of the two preimages.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-- Conjugating a pure quaternion by a unit quaternion `q` multiplies the corresponding
vector by `toRotationMatrix q`. -/
theorem mul_ofVector_mul_star {q : ℍ[ℝ]} (hq : normSq q = 1) (v : Fin 3 → ℝ) :
    q * ofVector v * star q = ofVector (toRotationMatrix q *ᵥ v) := by
  rw [normSq_def'] at hq
  ext <;>
    simp [ofVector, toRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ring
  · linear_combination (v 0) * hq
  · linear_combination (v 1) * hq
  · linear_combination (v 2) * hq

/-- `toRotationMatrix q` is the unique matrix of the conjugation action of `q`. -/
theorem toRotationMatrix_eq_iff_forall_conj {q : ℍ[ℝ]} (hq : normSq q = 1)
    {M : Matrix (Fin 3) (Fin 3) ℝ} :
    toRotationMatrix q = M ↔ ∀ v, q * ofVector v * star q = ofVector (M *ᵥ v) := by
  constructor
  · rintro rfl v
    exact mul_ofVector_mul_star hq v
  · intro h
    apply Matrix.mulVec_injective
    funext v
    exact ofVector_injective ((mul_ofVector_mul_star hq v).symm.trans (h v))

/-- The rotation matrix of the identity quaternion is the identity. -/
@[simp]
theorem toRotationMatrix_one : toRotationMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toRotationMatrix]

/-- The rotation matrix of the conjugate quaternion is the transpose. -/
theorem toRotationMatrix_star (q : ℍ[ℝ]) :
    toRotationMatrix (star q) = (toRotationMatrix q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toRotationMatrix] <;> ring

/-- `q` and `-q` have the same rotation matrix. -/
@[simp]
theorem toRotationMatrix_neg (q : ℍ[ℝ]) : toRotationMatrix (-q) = toRotationMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toRotationMatrix]

/-- Multiplying unit quaternions composes their rotations. -/
theorem toRotationMatrix_mul {p q : ℍ[ℝ]} (hp : normSq p = 1) (hq : normSq q = 1) :
    toRotationMatrix (p * q) = toRotationMatrix p * toRotationMatrix q := by
  have hpq : normSq (p * q) = 1 := by rw [map_mul, hp, hq, mul_one]
  rw [toRotationMatrix_eq_iff_forall_conj hpq]
  intro v
  rw [← Matrix.mulVec_mulVec, ← mul_ofVector_mul_star hp, ← mul_ofVector_mul_star hq,
    star_mul]
  simp only [mul_assoc]

/-- The rotation matrix of a unit quaternion lies in `SO(3)`. -/
theorem toRotationMatrix_mem_specialOrthogonalGroup {q : ℍ[ℝ]} (hq : normSq q = 1) :
    toRotationMatrix q ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  constructor
  · have hs : normSq (star q) = 1 := by rw [normSq_star, hq]
    have h1 : q * star q = 1 := by rw [self_mul_star, hq]; rfl
    rw [← toRotationMatrix_star, ← toRotationMatrix_mul hq hs, h1, toRotationMatrix_one]
  · rw [normSq_def'] at hq
    simp [toRotationMatrix, Matrix.det_fin_three]
    linear_combination 4 * (q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) * hq

/-- A unit quaternion represents its rotation matrix. -/
theorem representsRotation_toRotationMatrix {q : ℍ[ℝ]} (hq : normSq q = 1) :
    RepresentsRotation q (toRotationMatrix q) :=
  ⟨hq, mul_ofVector_mul_star hq⟩

/-- `q` represents `M` exactly when `q` is a unit quaternion with rotation matrix `M`. -/
theorem representsRotation_iff {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ} :
    RepresentsRotation q M ↔ normSq q = 1 ∧ toRotationMatrix q = M := by
  constructor
  · intro h
    exact ⟨h.normSq_eq_one,
      (toRotationMatrix_eq_iff_forall_conj h.normSq_eq_one).2 h.representsScaledRotation⟩
  · rintro ⟨hq, rfl⟩
    exact representsRotation_toRotationMatrix hq

/-- Two unit quaternions have the same rotation matrix exactly when they agree up to
sign. -/
theorem toRotationMatrix_eq_iff {p q : ℍ[ℝ]} (hp : normSq p = 1) (hq : normSq q = 1) :
    toRotationMatrix p = toRotationMatrix q ↔ p = q ∨ p = -q := by
  constructor
  · intro h
    exact (representsRotation_iff.2 ⟨hp, h⟩).eq_or_eq_neg (representsRotation_toRotationMatrix hq)
  · rintro (rfl | rfl)
    · rfl
    · exact toRotationMatrix_neg q

end SympyQuaternion
