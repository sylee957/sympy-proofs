module

public import SympyProofs.Quaternion.FromRotationMatrix.LeadingSign
public import SympyProofs.Quaternion.RepresentedMatrices

/-!
# A unit quaternion from a rotation matrix

`fromRotationMatrix M` is a unit quaternion for every rotation matrix `M`, given by a single
formula with no exceptional cases.

The ten products `4 qᵢ qⱼ` are linear in the entries of the matrix. The usual formula takes
`a = √(4a²) / 2 ≥ 0` and attaches `sign (4ab)`, `sign (4ac)`, `sign (4ad)` to the other
three square roots. This gives `0` whenever `a = 0`, that is for rotations by `π`. Here each
vanishing sign is replaced by the sign of the next product in the same row of `4 q qᵀ`,
through `leadingSign` of `FromRotationMatrix/LeadingSign.lean`.

The formula computes the solution of the specification `RepresentsRotation`:

* `RepresentsRotation.eq_fromRotationMatrix`: a sign-normalized quaternion representing
  `M` is `fromRotationMatrix M`.
* `representsRotation_fromRotationMatrix`: for `M ∈ SO(3)` the value represents `M`.
* `isSignNormalized_fromRotationMatrix`: its first nonzero component is positive.
* `eq_fromRotationMatrix_iff`: so it is the only sign-normalized quaternion representing
  `M`.

Round trips with `toRotationMatrix` of `ToRotationMatrix.lean`:

* `toRotationMatrix_fromRotationMatrix`: a rotation matrix is recovered.
* `fromRotationMatrix_toRotationMatrix`: a unit quaternion is recovered up to sign, and
  exactly if it is sign-normalized.

The version for scaled rotations, with the factor `det(M) ^ (1/3)`, is
`fromScaledRotationMatrix` of `FromRotationMatrix/ScaledSign.lean`.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-! ## The formula -/

/-- A unit quaternion for a rotation matrix: each square root takes the sign of the first
nonzero product relating it to an earlier component, and `+1` if there is none. -/
noncomputable def fromRotationMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) : ℍ[ℝ] :=
  -- The absolute values of the four components, from `4a²`, `4b²`, `4c²`, `4d²`.
  let absA := √(1 + M 0 0 + M 1 1 + M 2 2) / 2
  let absB := √(1 + M 0 0 - M 1 1 - M 2 2) / 2
  let absC := √(1 - M 0 0 + M 1 1 - M 2 2) / 2
  let absD := √(1 - M 0 0 - M 1 1 + M 2 2) / 2
  -- The six mixed products `4ab`, `4ac`, `4ad`, `4bc`, `4bd`, `4cd`.
  let ab := M 2 1 - M 1 2
  let ac := M 0 2 - M 2 0
  let ad := M 1 0 - M 0 1
  let bc := M 0 1 + M 1 0
  let bd := M 0 2 + M 2 0
  let cd := M 1 2 + M 2 1
  -- The sign of each component relative to the first nonzero earlier one.
  let signB := leadingSign [ab]
  let signC := leadingSign [ac, bc]
  let signD := leadingSign [ad, bd, cd]
  ⟨absA, absB * signB, absC * signC, absD * signD⟩

/-! ## The formula recovers a sign-normalized unit quaternion -/

/-- A sign-normalized quaternion representing `M` is `fromRotationMatrix M`. -/
theorem RepresentsRotation.eq_fromRotationMatrix {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsRotation q M) (n : IsSignNormalized q) : q = fromRotationMatrix M := by
  obtain ⟨hq, rfl⟩ := representsRotation_iff.1 h
  rw [normSq_def'] at hq
  obtain ⟨e0, e1, e2, e3⟩ := half_sqrt_mul_leadingSign_eq
    (a := q.re) (b := q.imI) (c := q.imJ) (d := q.imK)
    (t0 := 1 + toRotationMatrix q 0 0 + toRotationMatrix q 1 1 + toRotationMatrix q 2 2)
    (t1 := 1 + toRotationMatrix q 0 0 - toRotationMatrix q 1 1 - toRotationMatrix q 2 2)
    (t2 := 1 - toRotationMatrix q 0 0 + toRotationMatrix q 1 1 - toRotationMatrix q 2 2)
    (t3 := 1 - toRotationMatrix q 0 0 - toRotationMatrix q 1 1 + toRotationMatrix q 2 2)
    (u01 := toRotationMatrix q 2 1 - toRotationMatrix q 1 2)
    (u02 := toRotationMatrix q 0 2 - toRotationMatrix q 2 0)
    (u03 := toRotationMatrix q 1 0 - toRotationMatrix q 0 1)
    (u12 := toRotationMatrix q 0 1 + toRotationMatrix q 1 0)
    (u13 := toRotationMatrix q 0 2 + toRotationMatrix q 2 0)
    (u23 := toRotationMatrix q 1 2 + toRotationMatrix q 2 1)
    (by simp [toRotationMatrix]; linarith) (by simp [toRotationMatrix]; linarith)
    (by simp [toRotationMatrix]; linarith) (by simp [toRotationMatrix]; linarith)
    (by simp [toRotationMatrix]; ring) (by simp [toRotationMatrix]; ring)
    (by simp [toRotationMatrix]; ring) (by simp [toRotationMatrix]; ring)
    (by simp [toRotationMatrix]; ring) (by simp [toRotationMatrix]; ring) n
  ext <;> simp only [fromRotationMatrix]
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm

/-! ## The formula meets the specification -/

/-- `fromRotationMatrix M` represents `M`. -/
theorem representsRotation_fromRotationMatrix {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : RepresentsRotation (fromRotationMatrix M) M := by
  obtain ⟨q, hq⟩ := exists_representsRotation_iff.2 hM
  rcases isSignNormalized_or_neg hq.ne_zero with n | n
  · rw [← hq.eq_fromRotationMatrix n]
    exact hq
  · rw [← hq.neg.eq_fromRotationMatrix n]
    exact hq.neg

/-- The first nonzero component of `fromRotationMatrix M` is positive. -/
theorem isSignNormalized_fromRotationMatrix {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : IsSignNormalized (fromRotationMatrix M) := by
  obtain ⟨q, hq⟩ := exists_representsRotation_iff.2 hM
  rcases isSignNormalized_or_neg hq.ne_zero with n | n
  · rw [← hq.eq_fromRotationMatrix n]
    exact n
  · rw [← hq.neg.eq_fromRotationMatrix n]
    exact n

/-- `fromRotationMatrix M` is characterized by the specification: it is the sign-normalized
quaternion representing `M`. -/
theorem eq_fromRotationMatrix_iff {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) {q : ℍ[ℝ]} :
    q = fromRotationMatrix M ↔ RepresentsRotation q M ∧ IsSignNormalized q := by
  constructor
  · rintro rfl
    exact ⟨representsRotation_fromRotationMatrix hM, isSignNormalized_fromRotationMatrix hM⟩
  · rintro ⟨h, n⟩
    exact h.eq_fromRotationMatrix n

/-! ## Round trips with `toRotationMatrix` -/

/-- Converting a rotation matrix to a quaternion and back returns the matrix. -/
theorem toRotationMatrix_fromRotationMatrix {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    toRotationMatrix (fromRotationMatrix M) = M :=
  (representsRotation_iff.1 (representsRotation_fromRotationMatrix hM)).2

/-- The quaternion of a rotation matrix is a unit quaternion. -/
theorem normSq_fromRotationMatrix {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) : normSq (fromRotationMatrix M) = 1 :=
  (representsRotation_fromRotationMatrix hM).normSq_eq_one

/-- Converting a sign-normalized unit quaternion to a rotation matrix and back returns the
quaternion. -/
theorem fromRotationMatrix_toRotationMatrix_of_isSignNormalized {q : ℍ[ℝ]}
    (hq : normSq q = 1) (n : IsSignNormalized q) :
    fromRotationMatrix (toRotationMatrix q) = q :=
  ((representsRotation_toRotationMatrix hq).eq_fromRotationMatrix n).symm

/-- Converting a unit quaternion to a rotation matrix and back returns it up to sign. -/
theorem fromRotationMatrix_toRotationMatrix {q : ℍ[ℝ]} (hq : normSq q = 1) :
    fromRotationMatrix (toRotationMatrix q) = q ∨
      fromRotationMatrix (toRotationMatrix q) = -q := by
  have h := representsRotation_toRotationMatrix hq
  rcases isSignNormalized_or_neg h.ne_zero with n | n
  · exact Or.inl (h.eq_fromRotationMatrix n).symm
  · exact Or.inr (h.neg.eq_fromRotationMatrix n).symm

end SympyQuaternion
