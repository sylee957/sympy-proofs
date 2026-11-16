module

public import SympyProofs.Quaternion.RepresentsScaledRotation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The scaled rotation matrix of a quaternion

`toScaledRotationMatrix q` is the matrix of `v ↦ q v q*` for an arbitrary quaternion
`q = a + b i + c j + d k`. Its entries are homogeneous quadratic polynomials in the
components, and no division by the norm takes place, unlike in SymPy's
`Quaternion.to_rotation_matrix`.

* `mul_ofVector_mul_star_eq`:
  `q * ofVector v * star q = ofVector (toScaledRotationMatrix q *ᵥ v)`, for every `q`.
* `representsScaledRotation_iff`: `RepresentsScaledRotation q M ↔ toScaledRotationMatrix q = M`,
  so the matrix represented by a quaternion is `toScaledRotationMatrix q` and nothing else.
* `det_toScaledRotationMatrix`: its determinant is `normSq q ^ 3`.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-- The matrix of `v ↦ q v q*`, with no normalization. -/
def toScaledRotationMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := q.re
  let b := q.imI
  let c := q.imJ
  let d := q.imK
  -- The diagonal entries.
  let m00 := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
  let m11 := a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2
  let m22 := a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2
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

/-- Conjugating a pure quaternion with the conjugate of `q` multiplies the corresponding
vector by `toScaledRotationMatrix q`. -/
theorem mul_ofVector_mul_star_eq (q : ℍ[ℝ]) (v : Fin 3 → ℝ) :
    q * ofVector v * star q = ofVector (toScaledRotationMatrix q *ᵥ v) := by
  ext <;>
    simp [ofVector, toScaledRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- Every quaternion represents its scaled rotation matrix. -/
theorem representsScaledRotation_toScaledRotationMatrix (q : ℍ[ℝ]) :
    RepresentsScaledRotation q (toScaledRotationMatrix q) :=
  mul_ofVector_mul_star_eq q

/-- `q` represents `M` exactly when `M` is the scaled rotation matrix of `q`. -/
theorem representsScaledRotation_iff {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ} :
    RepresentsScaledRotation q M ↔ toScaledRotationMatrix q = M :=
  ⟨fun h => (representsScaledRotation_toScaledRotationMatrix q).matrix_unique h,
    fun h => h ▸ representsScaledRotation_toScaledRotationMatrix q⟩

/-- The determinant of the scaled rotation matrix is the cube of the squared norm. -/
theorem det_toScaledRotationMatrix (q : ℍ[ℝ]) :
    (toScaledRotationMatrix q).det = normSq q ^ 3 := by
  rw [normSq_def']
  simp [toScaledRotationMatrix, Matrix.det_fin_three]
  ring

end SympyQuaternion
