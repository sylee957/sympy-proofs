module

public import SympyProofs.Quaternion.RotationAction
public import SympyProofs.Quaternion.RotationMatrixSurjective

/-!
# Which matrices are represented, and by quaternions of which norm

General facts about the specifications `RepresentsRotation` and
`RepresentsScaledRotation` whose statements mention no formula, but whose proofs need one:
the explicit rotation matrix of a quaternion, to see that a represented matrix is a
rotation, and an explicit quaternion of a rotation, to see that every rotation is
represented. They therefore come after `RotationAction.lean` and
`RotationMatrixSurjective.lean`.

* `RepresentsRotation.mem_specialOrthogonalGroup`, `exists_representsRotation_iff`: the
  matrices represented by a unit quaternion are exactly those of `SO(3)`.
* `existsUnique_representsRotation_and_isSignNormalized`: each is represented by exactly
  one sign-normalized quaternion.
* `exists_representsScaledRotation_iff`: the matrices represented by some quaternion are
  exactly the scaled rotations `s • R`, with `0 ≤ s` and `R ∈ SO(3)`.
* `RepresentsScaledRotation.normSq_eq_of_smul`, `.normSq_pow_three`: the quaternion then
  has `normSq q = s`, that is `normSq q ^ 3 = det M`.
* `RepresentsScaledRotation.normSq_eq_one_iff`: it is a unit quaternion exactly when `M`
  is a rotation, so on `SO(3)` the scaled specification is the unit one
  (`representsScaledRotation_iff_representsRotation`).
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-! ## Rotations -/

/-- A matrix represented by a quaternion lies in `SO(3)`. -/
theorem RepresentsRotation.mem_specialOrthogonalGroup {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsRotation q M) : M ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  obtain ⟨hq, rfl⟩ := representsRotation_iff.1 h
  exact toRotationMatrix_mem_specialOrthogonalGroup hq

/-- The matrices represented by some quaternion are exactly those of `SO(3)`. -/
theorem exists_representsRotation_iff {M : Matrix (Fin 3) (Fin 3) ℝ} :
    (∃ q, RepresentsRotation q M) ↔ M ∈ specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨fun ⟨_, h⟩ => h.mem_specialOrthogonalGroup,
    fun hM =>
      let ⟨q, hq, h⟩ := exists_toRotationMatrix_eq hM
      ⟨q, representsRotation_iff.2 ⟨hq, h⟩⟩⟩

/-- Every matrix in `SO(3)` is represented by exactly one sign-normalized quaternion. -/
theorem existsUnique_representsRotation_and_isSignNormalized {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    ∃! q, RepresentsRotation q M ∧ IsSignNormalized q :=
  let ⟨_, hq⟩ := exists_representsRotation_iff.2 hM
  hq.existsUnique_isSignNormalized

/-! ## Scaled rotations -/

private theorem exists_representsScaledRotation_smul {s : ℝ} (hs : 0 ≤ s)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ q, RepresentsScaledRotation q (s • R) ∧ normSq q = s := by
  obtain ⟨q, hq⟩ := exists_representsRotation_iff.2 hR
  refine ⟨√s • q, ?_, ?_⟩
  · have h := hq.representsScaledRotation.smul (√s)
    rwa [Real.sq_sqrt hs] at h
  · rw [normSq_smul, hq.normSq_eq_one, mul_one, Real.sq_sqrt hs]

/-- The matrices represented by some quaternion, with no condition on its norm, are
exactly the nonnegative multiples of rotations. -/
theorem exists_representsScaledRotation_iff {M : Matrix (Fin 3) (Fin 3) ℝ} :
    (∃ q, RepresentsScaledRotation q M) ↔
      ∃ s : ℝ, 0 ≤ s ∧ ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, M = s • R := by
  constructor
  · rintro ⟨q, h⟩
    by_cases h0 : q = 0
    · exact ⟨0, le_rfl, 1, one_mem _, by rw [zero_smul]; exact h.eq_zero_iff.1 h0⟩
    · obtain ⟨c, -, hc2, u⟩ := h.exists_representsRotation_smul h0
      refine ⟨normSq q, normSq_nonneg, c ^ 2 • M, u.mem_specialOrthogonalGroup, ?_⟩
      rw [smul_smul, mul_comm, hc2, one_smul]
  · rintro ⟨s, hs, R, hR, rfl⟩
    obtain ⟨q, h, -⟩ := exists_representsScaledRotation_smul hs hR
    exact ⟨q, h⟩

/-- A quaternion representing `s • R` has squared norm `s`. -/
theorem RepresentsScaledRotation.normSq_eq_of_smul {q : ℍ[ℝ]} {s : ℝ} (hs : 0 ≤ s)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ)
    (h : RepresentsScaledRotation q (s • R)) : normSq q = s := by
  obtain ⟨p, hp, hn⟩ := exists_representsScaledRotation_smul hs hR
  rw [h.normSq_eq hp, hn]

/-- The squared norm of a representing quaternion is the cube root of the determinant. -/
theorem RepresentsScaledRotation.normSq_pow_three {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation q M) : normSq q ^ 3 = M.det := by
  obtain ⟨s, hs, R, hR, rfl⟩ := exists_representsScaledRotation_iff.1 ⟨q, h⟩
  rw [h.normSq_eq_of_smul hs hR, Matrix.det_smul, Fintype.card_fin,
    (mem_specialOrthogonalGroup_iff.mp hR).2, mul_one]

/-- A quaternion representing `M` is a unit quaternion exactly when `M` is a rotation. -/
theorem RepresentsScaledRotation.normSq_eq_one_iff {q : ℍ[ℝ]} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : RepresentsScaledRotation q M) :
    normSq q = 1 ↔ M ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  constructor
  · intro hq
    exact (RepresentsRotation.mk hq h).mem_specialOrthogonalGroup
  · intro hM
    have h' : RepresentsScaledRotation q ((1 : ℝ) • M) := by rwa [one_smul]
    exact h'.normSq_eq_of_smul zero_le_one hM

/-- On `SO(3)` the scaled specification is the unit one. -/
theorem representsScaledRotation_iff_representsRotation {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) :
    RepresentsScaledRotation q M ↔ RepresentsRotation q M :=
  ⟨fun h => ⟨h.normSq_eq_one_iff.2 hM, h⟩, fun h => h.representsScaledRotation⟩

end SympyQuaternion
