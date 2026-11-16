module

public import SympyProofs.Quaternion.RepresentsScaledRotation

/-!
# What it means for a unit quaternion to represent a rotation matrix

This file specializes the specification of `RepresentsScaledRotation.lean` to quaternions
of norm one. As there, no formula for a conversion appears.

* `RepresentsRotation q M`: `q` has norm one and `RepresentsScaledRotation q M`, that is,
  conjugation by `q` moves every vector the way `M` does,
  `q * ofVector v * star q = ofVector (M *ᵥ v)`. For a unit quaternion `star q = q⁻¹`.

Everything is inherited from the scaled specification through the field
`RepresentsRotation.representsScaledRotation`:

* `RepresentsRotation.matrix_unique`: a quaternion represents at most one matrix.
* `RepresentsRotation.one`, `.mul`, `.neg`: the identity, products, and negatives of
  representing quaternions represent the identity, products, and the same matrix.
* `RepresentsRotation.eq_or_eq_neg`: two quaternions representing the same matrix agree
  up to sign.
* `RepresentsRotation.eq_of_isSignNormalized`: with the sign rule they are equal.
* `RepresentsRotation.existsUnique_isSignNormalized`: if a matrix is represented at all,
  exactly one sign-normalized quaternion represents it.

Conversely `RepresentsScaledRotation.exists_representsRotation_smul` rescales a nonzero
quaternion of the scaled specification to one of this specification.
-/

@[expose] public section

namespace SympyQuaternion

open Matrix Quaternion

/-- `q` represents the rotation `M`: it is a unit quaternion that represents `M` as a
scaled rotation. -/
structure RepresentsRotation (q : ℍ[ℝ]) (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  /-- The quaternion has norm one. -/
  normSq_eq_one : normSq q = 1
  /-- Conjugation by the quaternion acts on vectors as the matrix. -/
  representsScaledRotation : RepresentsScaledRotation q M

namespace RepresentsRotation

variable {p q : ℍ[ℝ]} {M N : Matrix (Fin 3) (Fin 3) ℝ}

theorem ne_zero (h : RepresentsRotation q M) : q ≠ 0 := by
  rintro rfl
  simpa using h.normSq_eq_one

theorem mul_star_self (h : RepresentsRotation q M) : q * star q = 1 := by
  rw [self_mul_star, h.normSq_eq_one, coe_one]

theorem star_mul_self (h : RepresentsRotation q M) : star q * q = 1 := by
  rw [Quaternion.star_mul_self, h.normSq_eq_one, coe_one]

/-- A quaternion represents at most one matrix. -/
theorem matrix_unique (hM : RepresentsRotation q M) (hN : RepresentsRotation q N) : M = N :=
  hM.representsScaledRotation.matrix_unique hN.representsScaledRotation

/-- The identity quaternion represents the identity matrix. -/
protected theorem one : RepresentsRotation 1 1 :=
  ⟨map_one _, RepresentsScaledRotation.one⟩

/-- `q` and `-q` represent the same matrix. -/
protected theorem neg (h : RepresentsRotation q M) : RepresentsRotation (-q) M :=
  ⟨by rw [normSq_neg, h.normSq_eq_one], h.representsScaledRotation.neg⟩

/-- The product of two representing quaternions represents the product of the matrices. -/
protected theorem mul (hp : RepresentsRotation p M) (hq : RepresentsRotation q N) :
    RepresentsRotation (p * q) (M * N) :=
  ⟨by rw [map_mul, hp.normSq_eq_one, hq.normSq_eq_one, mul_one],
    hp.representsScaledRotation.mul hq.representsScaledRotation⟩

/-- Two quaternions representing the same matrix agree up to sign. -/
theorem eq_or_eq_neg (hp : RepresentsRotation p M) (hq : RepresentsRotation q M) :
    p = q ∨ p = -q :=
  hp.representsScaledRotation.eq_or_eq_neg hq.representsScaledRotation

/-- Two sign-normalized quaternions representing the same matrix are equal. -/
theorem eq_of_isSignNormalized (hp : RepresentsRotation p M) (hq : RepresentsRotation q M)
    (np : IsSignNormalized p) (nq : IsSignNormalized q) : p = q :=
  hp.representsScaledRotation.eq_of_isSignNormalized hq.representsScaledRotation np nq

/-- A matrix that is represented by some quaternion is represented by exactly one
sign-normalized quaternion. -/
theorem existsUnique_isSignNormalized (h : RepresentsRotation q M) :
    ∃! p, RepresentsRotation p M ∧ IsSignNormalized p := by
  rcases isSignNormalized_or_neg h.ne_zero with n | n
  · exact ⟨q, ⟨h, n⟩, fun p hp => hp.1.eq_of_isSignNormalized h hp.2 n⟩
  · exact ⟨-q, ⟨h.neg, n⟩, fun p hp => hp.1.eq_of_isSignNormalized h.neg hp.2 n⟩

end RepresentsRotation

/-- A nonzero representing quaternion is a positive multiple of a unit quaternion that
represents the correspondingly rescaled matrix. -/
theorem RepresentsScaledRotation.exists_representsRotation_smul {q : ℍ[ℝ]}
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : RepresentsScaledRotation q M) (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 * normSq q = 1 ∧ RepresentsRotation (c • q) (c ^ 2 • M) := by
  obtain ⟨c, hc, hc2⟩ := exists_pos_sq_mul_normSq_eq_one hq
  exact ⟨c, hc, hc2, by rw [normSq_smul, hc2], h.smul c⟩

end SympyQuaternion
