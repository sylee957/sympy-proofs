module

public import SympyProofs.Quaternion.OfVector
public import SympyProofs.Quaternion.IsSignNormalized
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul

/-!
# What it means for a quaternion to represent a scaled rotation matrix

This file states the basic specification of a matrix-to-quaternion conversion without any
formula for the conversion, and proves that the specification determines its answer up to
sign. The specification for unit quaternions in `RepresentsRotation.lean` is built on it.

A vector `v : ℝ³` is identified with the pure quaternion `ofVector v = v₀ i + v₁ j + v₂ k`
of `OfVector.lean`.

* `RepresentsScaledRotation q M`: the map `v ↦ q v q*` moves every vector the way `M`
  does, `q * ofVector v * star q = ofVector (M *ᵥ v)`.

Since `q v q*` multiplies lengths by `normSq q`, the single equation records a uniform
scaling as well as a rotation.

Consequences, none of which mention a formula:

* `RepresentsScaledRotation.matrix_unique`: a quaternion represents at most one matrix.
* `RepresentsScaledRotation.zero`, `.one`, `.mul`, `.neg`, `.smul`: zero, the identity,
  products, negatives and real multiples; scaling the quaternion by `c` scales the matrix
  by `c²`.
* `RepresentsScaledRotation.normSq_ofVector_mulVec`: the matrix scales squared lengths by
  `normSq q ^ 2`, so the norm of the quaternion is determined by the matrix
  (`RepresentsScaledRotation.normSq_eq`), and `q = 0 ↔ M = 0`
  (`RepresentsScaledRotation.eq_zero_iff`).
* `RepresentsScaledRotation.eq_or_eq_neg`: two quaternions representing the same matrix
  agree up to sign.
* `RepresentsScaledRotation.eq_of_isSignNormalized`: with the sign rule of
  `IsSignNormalized.lean` they are equal.
* `RepresentsScaledRotation.existsUnique_isSignNormalized`: a nonzero matrix that is
  represented at all is represented by exactly one sign-normalized quaternion. The zero
  matrix is represented only by `0`, which has no nonzero component to normalize.
* `existsUnique_representsScaledRotation_and_isSignNormalized_iff`: so there is exactly
  one sign-normalized solution when `M` is nonzero and represented, and none otherwise.

Which matrices are represented, and by which explicit formula, is the subject of the
other files in this directory.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-- `q` represents the scaled rotation `M`: the map `v ↦ q v q*` on vectors is
multiplication by `M`. No condition is imposed on the norm of `q`. -/
def RepresentsScaledRotation (q : ℍ[ℝ]) (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ v, q * ofVector v * star q = ofVector (M *ᵥ v)

/-- A nonzero quaternion has a positive real multiple of norm one. -/
theorem exists_pos_sq_mul_normSq_eq_one {q : ℍ[ℝ]} (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 * normSq q = 1 := by
  have hpos : 0 < normSq q := lt_of_le_of_ne normSq_nonneg (Ne.symm (mt normSq_eq_zero.1 hq))
  refine ⟨(√(normSq q))⁻¹, inv_pos.2 (Real.sqrt_pos.2 hpos), ?_⟩
  rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

namespace RepresentsScaledRotation

variable {p q : ℍ[ℝ]} {M N : Matrix (Fin 3) (Fin 3) ℝ}

/-- A quaternion represents at most one matrix. -/
theorem matrix_unique (hM : RepresentsScaledRotation q M)
    (hN : RepresentsScaledRotation q N) : M = N := by
  apply Matrix.mulVec_injective
  funext v
  exact ofVector_injective ((hM v).symm.trans (hN v))

/-- The zero quaternion represents the zero matrix. -/
protected theorem zero : RepresentsScaledRotation 0 0 :=
  fun v => by ext <;> simp [ofVector]

/-- The identity quaternion represents the identity matrix. -/
protected theorem one : RepresentsScaledRotation 1 1 :=
  fun v => by simp

/-- `q` and `-q` represent the same matrix. -/
protected theorem neg (h : RepresentsScaledRotation q M) : RepresentsScaledRotation (-q) M :=
  fun v => by rw [star_neg, neg_mul, neg_mul, mul_neg, neg_neg, h v]

/-- The product of two representing quaternions represents the product of the matrices. -/
protected theorem mul (hp : RepresentsScaledRotation p M) (hq : RepresentsScaledRotation q N) :
    RepresentsScaledRotation (p * q) (M * N) :=
  fun v => by
    rw [← Matrix.mulVec_mulVec, ← hp, ← hq, star_mul]
    simp only [mul_assoc]

/-- Scaling the quaternion by `c` scales the matrix by `c²`. -/
protected theorem smul (h : RepresentsScaledRotation q M) (c : ℝ) :
    RepresentsScaledRotation (c • q) (c ^ 2 • M) :=
  fun v => by
    rw [Matrix.smul_mulVec, ofVector_smul, ← h v, Quaternion.star_smul, smul_mul_assoc,
      smul_mul_assoc, mul_smul_comm, smul_smul, sq]

/-- The matrix multiplies squared lengths by `normSq q ^ 2`. -/
theorem normSq_ofVector_mulVec (h : RepresentsScaledRotation q M) (v : Fin 3 → ℝ) :
    normSq (ofVector (M *ᵥ v)) = normSq q ^ 2 * normSq (ofVector v) := by
  rw [← h v, map_mul, map_mul, normSq_star]
  ring

/-- The norm of a representing quaternion is determined by the matrix. -/
theorem normSq_eq (hp : RepresentsScaledRotation p M) (hq : RepresentsScaledRotation q M) :
    normSq p = normSq q := by
  have h1 := hp.normSq_ofVector_mulVec ![1, 0, 0]
  have h2 := hq.normSq_ofVector_mulVec ![1, 0, 0]
  exact (sq_eq_sq₀ normSq_nonneg normSq_nonneg).1
    (mul_right_cancel₀ (by simp [normSq_ofVector]) (h1.symm.trans h2))

/-- Only the zero quaternion represents the zero matrix, and it represents nothing else. -/
theorem eq_zero_iff (h : RepresentsScaledRotation q M) : q = 0 ↔ M = 0 := by
  constructor
  · rintro rfl
    exact h.matrix_unique RepresentsScaledRotation.zero
  · rintro rfl
    exact normSq_eq_zero.1 (h.normSq_eq RepresentsScaledRotation.zero ▸ map_zero _)

/-- Two unit quaternions representing the same matrix agree up to sign. -/
private theorem eq_or_eq_neg_of_normSq_eq_one (hp : RepresentsScaledRotation p M)
    (hq : RepresentsScaledRotation q M) (np : normSq p = 1) (nq : normSq q = 1) :
    p = q ∨ p = -q := by
  have hpp : star p * p = 1 := by rw [Quaternion.star_mul_self, np, coe_one]
  have hqq : star q * q = 1 := by rw [Quaternion.star_mul_self, nq, coe_one]
  have hqq' : q * star q = 1 := by rw [self_mul_star, nq, coe_one]
  obtain ⟨r, hr⟩ : ∃ r, r = star q * p := ⟨_, rfl⟩
  -- `r = q⁻¹ p` commutes with every pure quaternion.
  have comm : ∀ v, r * ofVector v = ofVector v * r := by
    intro v
    have h : p * ofVector v * star p = q * ofVector v * star q := (hp v).trans (hq v).symm
    calc r * ofVector v = star q * (p * ofVector v * star p) * p := by
          simp only [hr, mul_assoc, hpp, mul_one]
      _ = star q * (q * ofVector v * star q) * p := by rw [h]
      _ = ofVector v * r := by
          simp only [hr, mul_assoc]
          rw [← mul_assoc (star q) q, hqq, one_mul]
  -- Hence `r` is real.
  have c1 := comm ![1, 0, 0]
  have c2 := comm ![0, 1, 0]
  have hz : r.imK = 0 := by
    have := congrArg QuaternionAlgebra.imJ c1
    simp [ofVector] at this
    linarith
  have hy : r.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imK c1
    simp [ofVector] at this
    linarith
  have hx : r.imI = 0 := by
    have := congrArg QuaternionAlgebra.imK c2
    simp [ofVector] at this
    linarith
  -- It has norm one, so it is `1` or `-1`.
  have hn : normSq r = 1 := by rw [hr, map_mul, normSq_star, np, nq, mul_one]
  rw [normSq_def', hx, hy, hz] at hn
  have hre : (r.re - 1) * (r.re + 1) = 0 := by linear_combination hn
  have hpq : p = q * r := by rw [hr, ← mul_assoc, hqq', one_mul]
  rcases mul_eq_zero.1 hre with h | h
  · left
    have h1 : r = 1 := by ext <;> simp [hx, hy, hz]; linarith
    rw [hpq, h1, mul_one]
  · right
    have h1 : r = -1 := by ext <;> simp [hx, hy, hz]; linarith
    rw [hpq, h1, mul_neg, mul_one]

/-- Two quaternions representing the same matrix agree up to sign. -/
theorem eq_or_eq_neg (hp : RepresentsScaledRotation p M) (hq : RepresentsScaledRotation q M) :
    p = q ∨ p = -q := by
  by_cases h0 : q = 0
  · left
    rw [h0]
    exact hp.eq_zero_iff.2 (hq.eq_zero_iff.1 h0)
  · -- Rescale both to norm one.
    obtain ⟨c, hc, hc2⟩ := exists_pos_sq_mul_normSq_eq_one h0
    rcases eq_or_eq_neg_of_normSq_eq_one (hp.smul c) (hq.smul c)
      (by rw [normSq_smul, hp.normSq_eq hq, hc2]) (by rw [normSq_smul, hc2]) with h | h
    · exact Or.inl (smul_right_injective _ hc.ne' h)
    · rw [← smul_neg] at h
      exact Or.inr (smul_right_injective _ hc.ne' h)

/-- Two sign-normalized quaternions representing the same matrix are equal. -/
theorem eq_of_isSignNormalized (hp : RepresentsScaledRotation p M)
    (hq : RepresentsScaledRotation q M) (np : IsSignNormalized p)
    (nq : IsSignNormalized q) : p = q := by
  rcases hp.eq_or_eq_neg hq with h | h
  · exact h
  · exact absurd (h ▸ np) nq.not_neg

/-- A nonzero matrix that is represented by some quaternion is represented by exactly one
sign-normalized quaternion. -/
theorem existsUnique_isSignNormalized (h : RepresentsScaledRotation q M) (hM : M ≠ 0) :
    ∃! p, RepresentsScaledRotation p M ∧ IsSignNormalized p := by
  rcases isSignNormalized_or_neg (mt h.eq_zero_iff.1 hM) with n | n
  · exact ⟨q, ⟨h, n⟩, fun p hp => hp.1.eq_of_isSignNormalized h hp.2 n⟩
  · exact ⟨-q, ⟨h.neg, n⟩, fun p hp => hp.1.eq_of_isSignNormalized h.neg hp.2 n⟩

end RepresentsScaledRotation

/-- The zero matrix is represented only by the zero quaternion. -/
theorem representsScaledRotation_zero_iff {q : ℍ[ℝ]} : RepresentsScaledRotation q 0 ↔ q = 0 :=
  ⟨fun h => h.eq_zero_iff.2 rfl, fun h => h ▸ RepresentsScaledRotation.zero⟩

/-- The scaled specification with the sign rule has exactly one solution when `M` is
nonzero and represented, and no solution otherwise. -/
theorem existsUnique_representsScaledRotation_and_isSignNormalized_iff
    {M : Matrix (Fin 3) (Fin 3) ℝ} :
    (∃! q, RepresentsScaledRotation q M ∧ IsSignNormalized q) ↔
      M ≠ 0 ∧ ∃ q, RepresentsScaledRotation q M := by
  constructor
  · rintro ⟨q, ⟨h, n⟩, -⟩
    refine ⟨fun hM => ?_, q, h⟩
    exact not_isSignNormalized_zero (h.eq_zero_iff.2 hM ▸ n)
  · rintro ⟨hM, q, h⟩
    exact h.existsUnique_isSignNormalized hM

end SympyQuaternion
