module

public import SympyProofs.Quaternion.ToScaledRotationMatrix
public import SympyProofs.Quaternion.FromRotationMatrix.Sign
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A quaternion from a scaled rotation matrix

`fromScaledRotationMatrix` is a replacement for SymPy's `Quaternion.from_rotation_matrix`
with no exceptional cases, including its scaling factor `det(M) ^ (1/3)`. On rotation
matrices it is `fromRotationMatrix` of `FromRotationMatrix/Sign.lean`.

SymPy's formula takes `a = √(4a²) / 2 ≥ 0` and attaches `sign (4ab)`, `sign (4ac)`,
`sign (4ad)` to the other three square roots, where the ten products `4 qᵢ qⱼ` are linear
in the entries of the matrix and in `det(M) ^ (1/3)`. This gives `0` whenever `a = 0`, that
is for rotations by `π` (sympy/sympy#31130). Here each vanishing sign is replaced by the
sign of the next product in the same row of `4 q qᵀ`, through `leadingSign` of
`FromRotationMatrix/LeadingSign.lean`.

The formula computes the solution of the specification wherever one exists:

* `RepresentsScaledRotation.eq_fromScaledRotationMatrix`: a sign-normalized quaternion
  representing `M` is `fromScaledRotationMatrix M`.
* `fromScaledRotationMatrix_represents`: if any quaternion represents `M`, the formula's
  value does.
* `fromScaledRotationMatrix_isSignNormalized`: if moreover `M ≠ 0`, the value is
  sign-normalized.
* `eq_fromScaledRotationMatrix_iff`: so among sign-normalized quaternions it is the only
  one representing `M`.
* `eq_fromScaledRotationMatrix_zero_iff`: for the zero matrix it is the only quaternion
  representing it.
* `fromScaledRotationMatrix_unique`: any function meeting the specification on represented
  matrices, the zero matrix included, agrees with it there.

Round trips with `toScaledRotationMatrix` of `ToScaledRotationMatrix.lean`:

* `toScaledRotationMatrix_fromScaledRotationMatrix`: a represented matrix is recovered.
* `fromScaledRotationMatrix_toScaledRotationMatrix`: a quaternion is recovered up to sign,
  and exactly if it is sign-normalized.

Relation to `fromRotationMatrix`:

* `fromScaledRotationMatrix_eq_fromRotationMatrix`: for `M ∈ SO(3)` the two formulas
  agree.
* `fromScaledRotationMatrix_smul`: `fromScaledRotationMatrix (s • R)` is
  `√s • fromRotationMatrix R` for `0 ≤ s` and `R ∈ SO(3)`.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-! ## The formula -/

/-- `Quaternion.from_rotation_matrix` with its scaling factor and with `sign` replaced by
`leadingSign`: each square root takes the sign of the first nonzero product relating it to
an earlier component, and `+1` if there is none. -/
noncomputable def fromScaledRotationMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) : ℍ[ℝ] :=
  let scale := M.det ^ ((1 : ℝ) / 3)
  -- The absolute values of the four components, from `4a²`, `4b²`, `4c²`, `4d²`.
  let absA := √(scale + M 0 0 + M 1 1 + M 2 2) / 2
  let absB := √(scale + M 0 0 - M 1 1 - M 2 2) / 2
  let absC := √(scale - M 0 0 + M 1 1 - M 2 2) / 2
  let absD := √(scale - M 0 0 - M 1 1 + M 2 2) / 2
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

@[simp]
theorem fromScaledRotationMatrix_zero : fromScaledRotationMatrix 0 = 0 := by
  ext <;> simp [fromScaledRotationMatrix]

/-! ## The formula recovers a sign-normalized quaternion -/

/-- A sign-normalized quaternion representing `M` is `fromScaledRotationMatrix M`. -/
theorem RepresentsScaledRotation.eq_fromScaledRotationMatrix {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M)
    (n : IsSignNormalized q) : q = fromScaledRotationMatrix M := by
  obtain rfl := representsScaledRotation_iff.1 h
  have hk : (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) = normSq q := by
    rw [det_toScaledRotationMatrix, one_div]
    exact Real.pow_rpow_inv_natCast normSq_nonneg (by norm_num)
  have hN := normSq_def' (a := q)
  obtain ⟨e0, e1, e2, e3⟩ := half_sqrt_mul_leadingSign_eq
    (a := q.re) (b := q.imI) (c := q.imJ) (d := q.imK)
    (t0 := (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) + toScaledRotationMatrix q 0 0 +
      toScaledRotationMatrix q 1 1 + toScaledRotationMatrix q 2 2)
    (t1 := (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) + toScaledRotationMatrix q 0 0 -
      toScaledRotationMatrix q 1 1 - toScaledRotationMatrix q 2 2)
    (t2 := (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) - toScaledRotationMatrix q 0 0 +
      toScaledRotationMatrix q 1 1 - toScaledRotationMatrix q 2 2)
    (t3 := (toScaledRotationMatrix q).det ^ ((1 : ℝ) / 3) - toScaledRotationMatrix q 0 0 -
      toScaledRotationMatrix q 1 1 + toScaledRotationMatrix q 2 2)
    (u01 := toScaledRotationMatrix q 2 1 - toScaledRotationMatrix q 1 2)
    (u02 := toScaledRotationMatrix q 0 2 - toScaledRotationMatrix q 2 0)
    (u03 := toScaledRotationMatrix q 1 0 - toScaledRotationMatrix q 0 1)
    (u12 := toScaledRotationMatrix q 0 1 + toScaledRotationMatrix q 1 0)
    (u13 := toScaledRotationMatrix q 0 2 + toScaledRotationMatrix q 2 0)
    (u23 := toScaledRotationMatrix q 1 2 + toScaledRotationMatrix q 2 1)
    (by rw [hk, hN]; simp [toScaledRotationMatrix]; ring)
    (by rw [hk, hN]; simp [toScaledRotationMatrix]; ring)
    (by rw [hk, hN]; simp [toScaledRotationMatrix]; ring)
    (by rw [hk, hN]; simp [toScaledRotationMatrix]; ring)
    (by simp [toScaledRotationMatrix]; ring) (by simp [toScaledRotationMatrix]; ring)
    (by simp [toScaledRotationMatrix]; ring) (by simp [toScaledRotationMatrix]; ring)
    (by simp [toScaledRotationMatrix]; ring) (by simp [toScaledRotationMatrix]; ring) n
  ext <;> simp only [fromScaledRotationMatrix]
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm

/-! ## The formula meets the specification -/

/-- If any quaternion represents `M`, then `fromScaledRotationMatrix M` does. -/
theorem fromScaledRotationMatrix_represents {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation q M) :
    RepresentsScaledRotation (fromScaledRotationMatrix M) M := by
  by_cases h0 : q = 0
  · obtain rfl := h.eq_zero_iff.1 h0
    rw [fromScaledRotationMatrix_zero]
    exact RepresentsScaledRotation.zero
  · rcases isSignNormalized_or_neg h0 with n | n
    · rw [← h.eq_fromScaledRotationMatrix n]
      exact h
    · rw [← h.neg.eq_fromScaledRotationMatrix n]
      exact h.neg

/-- If any quaternion represents `M ≠ 0`, then `fromScaledRotationMatrix M` is
sign-normalized. -/
theorem fromScaledRotationMatrix_isSignNormalized {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation q M) (hM : M ≠ 0) :
    IsSignNormalized (fromScaledRotationMatrix M) := by
  rcases isSignNormalized_or_neg (mt h.eq_zero_iff.1 hM) with n | n
  · rw [← h.eq_fromScaledRotationMatrix n]
    exact n
  · rw [← h.neg.eq_fromScaledRotationMatrix n]
    exact n

/-- For a represented matrix, a sign-normalized quaternion is `fromScaledRotationMatrix M`
exactly when it represents `M`. -/
theorem eq_fromScaledRotationMatrix_iff {p q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation p M) (n : IsSignNormalized q) :
    q = fromScaledRotationMatrix M ↔ RepresentsScaledRotation q M := by
  constructor
  · rintro rfl
    exact fromScaledRotationMatrix_represents h
  · intro hq
    exact hq.eq_fromScaledRotationMatrix n

/-- For the zero matrix, `fromScaledRotationMatrix 0` is the only quaternion representing
it. No sign rule is involved. -/
theorem eq_fromScaledRotationMatrix_zero_iff {q : ℍ[ℝ]} :
    q = fromScaledRotationMatrix 0 ↔ RepresentsScaledRotation q 0 := by
  rw [fromScaledRotationMatrix_zero]
  exact representsScaledRotation_zero_iff.symm

/-- Any function that meets the specification on represented matrices agrees with
`fromScaledRotationMatrix` on all of them, the zero matrix included. -/
theorem fromScaledRotationMatrix_unique {f : Matrix (Fin 3) (Fin 3) ℝ → ℍ[ℝ]}
    (hf : ∀ M p, RepresentsScaledRotation p M →
      RepresentsScaledRotation (f M) M ∧ (M ≠ 0 → IsSignNormalized (f M)))
    {p : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation p M) :
    f M = fromScaledRotationMatrix M := by
  obtain ⟨hr, hn⟩ := hf M p h
  by_cases hM : M = 0
  · subst hM
    exact eq_fromScaledRotationMatrix_zero_iff.2 hr
  · exact (eq_fromScaledRotationMatrix_iff h (hn hM)).2 hr

/-! ## Round trips with `toScaledRotationMatrix` -/

/-- Converting a represented matrix to a quaternion and back returns the matrix. -/
theorem toScaledRotationMatrix_fromScaledRotationMatrix {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M) :
    toScaledRotationMatrix (fromScaledRotationMatrix M) = M :=
  representsScaledRotation_iff.1 (fromScaledRotationMatrix_represents h)

/-- Converting a sign-normalized quaternion to a matrix and back returns the quaternion. -/
theorem fromScaledRotationMatrix_toScaledRotationMatrix_of_isSignNormalized {q : ℍ[ℝ]}
    (n : IsSignNormalized q) : fromScaledRotationMatrix (toScaledRotationMatrix q) = q :=
  ((representsScaledRotation_toScaledRotationMatrix q).eq_fromScaledRotationMatrix n).symm

/-- Converting any quaternion to a matrix and back returns it up to sign. -/
theorem fromScaledRotationMatrix_toScaledRotationMatrix (q : ℍ[ℝ]) :
    fromScaledRotationMatrix (toScaledRotationMatrix q) = q ∨
      fromScaledRotationMatrix (toScaledRotationMatrix q) = -q := by
  have h := representsScaledRotation_toScaledRotationMatrix q
  by_cases h0 : q = 0
  · left
    rw [h.eq_zero_iff.1 h0, fromScaledRotationMatrix_zero, h0]
  · rcases isSignNormalized_or_neg h0 with n | n
    · exact Or.inl (h.eq_fromScaledRotationMatrix n).symm
    · exact Or.inr (h.neg.eq_fromScaledRotationMatrix n).symm

/-! ## Relation to `fromRotationMatrix` -/

/-- On `SO(3)` the scaling factor is `1`, and the formula is `fromRotationMatrix`. -/
theorem fromScaledRotationMatrix_eq_fromRotationMatrix {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    fromScaledRotationMatrix M = fromRotationMatrix M := by
  simp only [fromScaledRotationMatrix, fromRotationMatrix,
    (mem_specialOrthogonalGroup_iff.mp hM).2, Real.one_rpow]

/-- The quaternion of a scaled rotation is the scaled quaternion of the rotation. -/
theorem fromScaledRotationMatrix_smul {s : ℝ} (hs : 0 ≤ s) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    fromScaledRotationMatrix (s • R) = √s • fromRotationMatrix R := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · have h := (representsRotation_fromRotationMatrix hR).representsScaledRotation.smul (√s)
    rw [Real.sq_sqrt hs.le] at h
    exact (h.eq_fromScaledRotationMatrix
      ((isSignNormalized_fromRotationMatrix hR).smul (Real.sqrt_pos.2 hs))).symm

end SympyQuaternion
