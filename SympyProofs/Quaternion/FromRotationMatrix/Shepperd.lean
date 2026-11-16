module

public import SympyProofs.Quaternion.FromRotationMatrix.Sign

/-!
# Shepperd's method for a unit quaternion from a rotation matrix

`fromRotationMatrixShepperd` is the standard numerical conversion: among the four
squares `4a²`, `4b²`, `4c²`, `4d²` determined by the matrix it takes the largest as a
pivot, computes that component by a square root, and obtains the other three by dividing
the corresponding row of `4 q qᵀ` by the pivot component. The squares sum to `4`, so the
pivot is at least `1` and the division is safe for every rotation matrix.

The matrix `4 q qᵀ` is `productMatrix M`. The pivot row is selected by `max` and
`Real.sign`, so that a single expression serves all four cases.

The method makes the pivot component positive, not the first nonzero one, so its value
follows no fixed sign rule:

* `RepresentsRotation.fromRotationMatrixShepperd_eq_or_eq_neg`: for a quaternion `q`
  representing `M` it returns `q` or `-q`.
* `representsRotation_fromRotationMatrixShepperd`: for `M ∈ SO(3)` the value represents
  `M`.
* `fromRotationMatrixShepperd_eq_or_eq_neg_fromRotationMatrix`: it agrees with
  `fromRotationMatrix` up to sign.

`max` alone cannot select the row: it is continuous, and the value jumps where the pivot
row changes to a component of the opposite sign. `Real.sign` supplies the jump.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-! ## The formula -/

/-- The symmetric matrix `4 q qᵀ` of the quaternion of a rotation matrix. Its entries are
linear in the entries of the rotation matrix. -/
def productMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -- The diagonal: `4a²`, `4b²`, `4c²`, `4d²`.
  let aa := 1 + M 0 0 + M 1 1 + M 2 2
  let bb := 1 + M 0 0 - M 1 1 - M 2 2
  let cc := 1 - M 0 0 + M 1 1 - M 2 2
  let dd := 1 - M 0 0 - M 1 1 + M 2 2
  -- The off-diagonal entries: `4ab`, `4ac`, `4ad`, `4bc`, `4bd`, `4cd`.
  let ab := M 2 1 - M 1 2
  let ac := M 0 2 - M 2 0
  let ad := M 1 0 - M 0 1
  let bc := M 0 1 + M 1 0
  let bd := M 0 2 + M 2 0
  let cd := M 1 2 + M 2 1
  !![aa, ab, ac, ad;
    ab, bb, bc, bd;
    ac, bc, cc, cd;
    ad, bd, cd, dd]

/-- Shepperd's method: normalize the row of `4 q qᵀ` with the largest diagonal entry.

The row is selected by arithmetic on `max` and `Real.sign`, with no comparison deciding
between cases: `1 - Real.sign (largest - x) ^ 2` is `1` when `x` attains the maximum and
`0` otherwise. -/
noncomputable def fromRotationMatrixShepperd (M : Matrix (Fin 3) (Fin 3) ℝ) : ℍ[ℝ] :=
  let P := productMatrix M
  -- The largest diagonal entry.
  let largest := max (max (P 0 0) (P 1 1)) (max (P 2 2) (P 3 3))
  -- Indicators of the first row whose diagonal entry is the largest.
  let isA := 1 - Real.sign (largest - P 0 0) ^ 2
  let isB := (1 - isA) * (1 - Real.sign (largest - P 1 1) ^ 2)
  let isC := (1 - isA - isB) * (1 - Real.sign (largest - P 2 2) ^ 2)
  let isD := 1 - isA - isB - isC
  -- That row, and the absolute value of its component.
  let row := fun k => isA * P 0 k + isB * P 1 k + isC * P 2 k + isD * P 3 k
  let pivot := √largest / 2
  ⟨row 0 / (4 * pivot), row 1 / (4 * pivot), row 2 / (4 * pivot), row 3 / (4 * pivot)⟩

/-! ## The value is the quaternion up to sign -/

private theorem half_sqrt_of_pos {x : ℝ} (hx : 0 < x) : √(4 * (x * x)) / 2 = x := by
  rw [show 4 * (x * x) = (2 * x) * (2 * x) by ring, Real.sqrt_mul_self (by positivity)]
  ring

private theorem half_sqrt_of_neg {x : ℝ} (hx : x < 0) : √(4 * (x * x)) / 2 = -x := by
  rw [show 4 * (x * x) = (-(2 * x)) * (-(2 * x)) by ring,
    Real.sqrt_mul_self (by linarith)]
  ring

/-- Normalizing any row of `4 q qᵀ` whose component is nonzero returns the quaternion or
its negative. -/
private theorem pivotRow_eq_or_eq_neg (v : Fin 4 → ℝ) {i : Fin 4} (hi : v i ≠ 0) :
    let pivot := √(4 * (v i * v i)) / 2
    let r : ℍ[ℝ] := ⟨4 * (v i * v 0) / (4 * pivot), 4 * (v i * v 1) / (4 * pivot),
      4 * (v i * v 2) / (4 * pivot), 4 * (v i * v 3) / (4 * pivot)⟩
    r = ⟨v 0, v 1, v 2, v 3⟩ ∨ r = -⟨v 0, v 1, v 2, v 3⟩ := by
  intro pivot r
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · right
    simp only [r, pivot, half_sqrt_of_neg hneg]
    ext <;> simp <;> field_simp
  · left
    simp only [r, pivot, half_sqrt_of_pos hpos]
    ext <;> simp <;> field_simp

/-- For a unit quaternion, `productMatrix` of its rotation matrix is `4 q qᵀ`. -/
theorem productMatrix_toRotationMatrix {q : ℍ[ℝ]} (hq : normSq q = 1) :
    productMatrix (toRotationMatrix q) =
      Matrix.of fun j k =>
        4 * (![q.re, q.imI, q.imJ, q.imK] j * ![q.re, q.imI, q.imJ, q.imK] k) := by
  rw [normSq_def'] at hq
  ext j k
  fin_cases j <;> fin_cases k <;> simp [productMatrix, toRotationMatrix] <;> linarith

/-- Selecting the first row of `4 q qᵀ` with the largest diagonal entry by `max` and
`Real.sign`, and normalizing it, returns the quaternion or its negative. -/
private theorem maxRow_eq_or_eq_neg (v : Fin 4 → ℝ)
    (hN : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1) :
    let largest := max (max (4 * (v 0 * v 0)) (4 * (v 1 * v 1)))
      (max (4 * (v 2 * v 2)) (4 * (v 3 * v 3)))
    let isA := 1 - Real.sign (largest - 4 * (v 0 * v 0)) ^ 2
    let isB := (1 - isA) * (1 - Real.sign (largest - 4 * (v 1 * v 1)) ^ 2)
    let isC := (1 - isA - isB) * (1 - Real.sign (largest - 4 * (v 2 * v 2)) ^ 2)
    let isD := 1 - isA - isB - isC
    let row := fun k => isA * (4 * (v 0 * v k)) + isB * (4 * (v 1 * v k)) +
      isC * (4 * (v 2 * v k)) + isD * (4 * (v 3 * v k))
    let pivot := √largest / 2
    let r : ℍ[ℝ] :=
      ⟨row 0 / (4 * pivot), row 1 / (4 * pivot), row 2 / (4 * pivot), row 3 / (4 * pivot)⟩
    r = ⟨v 0, v 1, v 2, v 3⟩ ∨ r = -⟨v 0, v 1, v 2, v 3⟩ := by
  intro largest isA isB isC isD row pivot r
  have hle0 : 4 * (v 0 * v 0) ≤ largest := le_max_of_le_left (le_max_left _ _)
  have hle1 : 4 * (v 1 * v 1) ≤ largest := le_max_of_le_left (le_max_right _ _)
  have hle2 : 4 * (v 2 * v 2) ≤ largest := le_max_of_le_right (le_max_left _ _)
  have hle3 : 4 * (v 3 * v 3) ≤ largest := le_max_of_le_right (le_max_right _ _)
  -- A component attaining the maximum is nonzero, since the four squares sum to `1`.
  have hnz : ∀ i, 4 * (v i * v i) = largest → v i ≠ 0 := by
    intro i hi h0
    rw [h0] at hi
    linarith
  by_cases h0 : 4 * (v 0 * v 0) = largest
  · have eA : isA = 1 := by simp [isA, h0]
    have eB : isB = 0 := by simp [isB, eA]
    have eC : isC = 0 := by simp [isC, eA, eB]
    have eD : isD = 0 := by simp [isD, eA, eB, eC]
    have key := pivotRow_eq_or_eq_neg v (hnz 0 h0)
    simp only [r, row, pivot, eA, eB, eC, eD, ← h0, one_mul, zero_mul, add_zero]
    exact key
  · have lt0 : 4 * (v 0 * v 0) < largest := lt_of_le_of_ne hle0 h0
    have eA : isA = 0 := by simp [isA, Real.sign_of_pos (sub_pos.2 lt0)]
    by_cases h1 : 4 * (v 1 * v 1) = largest
    · have eB : isB = 1 := by simp [isB, eA, h1]
      have eC : isC = 0 := by simp [isC, eA, eB]
      have eD : isD = 0 := by simp [isD, eA, eB, eC]
      have key := pivotRow_eq_or_eq_neg v (hnz 1 h1)
      simp only [r, row, pivot, eA, eB, eC, eD, ← h1, one_mul, zero_mul, add_zero, zero_add]
      exact key
    · have lt1 : 4 * (v 1 * v 1) < largest := lt_of_le_of_ne hle1 h1
      have eB : isB = 0 := by simp [isB, eA, Real.sign_of_pos (sub_pos.2 lt1)]
      by_cases h2 : 4 * (v 2 * v 2) = largest
      · have eC : isC = 1 := by simp [isC, eA, eB, h2]
        have eD : isD = 0 := by simp [isD, eA, eB, eC]
        have key := pivotRow_eq_or_eq_neg v (hnz 2 h2)
        simp only [r, row, pivot, eA, eB, eC, eD, ← h2, one_mul, zero_mul, add_zero, zero_add]
        exact key
      · have lt2 : 4 * (v 2 * v 2) < largest := lt_of_le_of_ne hle2 h2
        have eC : isC = 0 := by simp [isC, eA, eB, Real.sign_of_pos (sub_pos.2 lt2)]
        have eD : isD = 1 := by simp [isD, eA, eB, eC]
        -- The maximum is attained, so it is attained by the last row.
        have h3 : 4 * (v 3 * v 3) = largest := by
          by_contra h3
          exact lt_irrefl largest
            (max_lt (max_lt lt0 lt1) (max_lt lt2 (lt_of_le_of_ne hle3 h3)))
        have key := pivotRow_eq_or_eq_neg v (hnz 3 h3)
        simp only [r, row, pivot, eA, eB, eC, eD, ← h3, one_mul, zero_mul, add_zero, zero_add]
        exact key

/-- For a quaternion `q` representing `M`, Shepperd's method returns `q` or `-q`. -/
theorem RepresentsRotation.fromRotationMatrixShepperd_eq_or_eq_neg {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsRotation q M) :
    fromRotationMatrixShepperd M = q ∨ fromRotationMatrixShepperd M = -q := by
  obtain ⟨hq, rfl⟩ := representsRotation_iff.1 h
  have hN := hq
  rw [normSq_def'] at hN
  have key := maxRow_eq_or_eq_neg ![q.re, q.imI, q.imJ, q.imK] hN
  simp only [fromRotationMatrixShepperd, productMatrix_toRotationMatrix hq, Matrix.of_apply]
  exact key

/-! ## The formula meets the specification up to the sign rule -/

/-- `fromRotationMatrixShepperd M` represents `M`. -/
theorem representsRotation_fromRotationMatrixShepperd {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    RepresentsRotation (fromRotationMatrixShepperd M) M := by
  obtain ⟨q, hq⟩ := exists_representsRotation_iff.2 hM
  rcases hq.fromRotationMatrixShepperd_eq_or_eq_neg with h | h
  · rw [h]
    exact hq
  · rw [h]
    exact hq.neg

/-- Shepperd's method agrees with `fromRotationMatrix` up to sign. -/
theorem fromRotationMatrixShepperd_eq_or_eq_neg_fromRotationMatrix
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    fromRotationMatrixShepperd M = fromRotationMatrix M ∨
      fromRotationMatrixShepperd M = -fromRotationMatrix M :=
  (representsRotation_fromRotationMatrix hM).fromRotationMatrixShepperd_eq_or_eq_neg

/-- Converting a rotation matrix to a quaternion by Shepperd's method and back returns the
matrix. -/
theorem toRotationMatrix_fromRotationMatrixShepperd {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    toRotationMatrix (fromRotationMatrixShepperd M) = M :=
  (representsRotation_iff.1 (representsRotation_fromRotationMatrixShepperd hM)).2

end SympyQuaternion
