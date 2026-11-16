module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic

/-!
# The sign rule for choosing between `q` and `-q`

A quaternion and its negative act on vectors in the same way, so a specification based on
the action determines a quaternion only up to sign. `IsSignNormalized q` selects one of
the two: the first nonzero component of `q`, in the order `re`, `imI`, `imJ`, `imK`, is
positive.

* `IsSignNormalized.not_neg`: at most one of `q` and `-q` is sign-normalized.
* `isSignNormalized_or_neg`: for `q ≠ 0`, at least one of them is.
* `not_isSignNormalized_zero`: the zero quaternion is not.
* `IsSignNormalized.smul`: positive multiples stay sign-normalized.
-/

@[expose] public section

namespace SympyQuaternion

open Quaternion

/-- The first nonzero component of the quaternion is positive. -/
def IsSignNormalized (q : ℍ[ℝ]) : Prop :=
  0 < q.re ∨ q.re = 0 ∧ (0 < q.imI ∨ q.imI = 0 ∧ (0 < q.imJ ∨ q.imJ = 0 ∧ 0 < q.imK))

namespace IsSignNormalized

variable {q : ℍ[ℝ]}

/-- At most one of `q` and `-q` is sign-normalized. -/
theorem not_neg (h : IsSignNormalized q) : ¬IsSignNormalized (-q) := by
  intro h'
  unfold IsSignNormalized at h h'
  simp only [re_neg, imI_neg, imJ_neg, imK_neg] at h'
  rcases h with h | ⟨h0, h | ⟨h1, h | ⟨h2, h⟩⟩⟩ <;>
    rcases h' with h' | ⟨h0', h' | ⟨h1', h' | ⟨h2', h'⟩⟩⟩ <;> linarith

end IsSignNormalized

/-- For a nonzero quaternion, one of `q` and `-q` is sign-normalized. -/
theorem isSignNormalized_or_neg {q : ℍ[ℝ]} (hq : q ≠ 0) :
    IsSignNormalized q ∨ IsSignNormalized (-q) := by
  unfold IsSignNormalized
  simp only [re_neg, imI_neg, imJ_neg, imK_neg]
  rcases lt_trichotomy q.re 0 with h0 | h0 | h0
  · exact Or.inr (Or.inl (by linarith))
  · rcases lt_trichotomy q.imI 0 with h1 | h1 | h1
    · exact Or.inr (Or.inr ⟨by linarith, Or.inl (by linarith)⟩)
    · rcases lt_trichotomy q.imJ 0 with h2 | h2 | h2
      · exact Or.inr (Or.inr ⟨by linarith, Or.inr ⟨by linarith, Or.inl (by linarith)⟩⟩)
      · rcases lt_trichotomy q.imK 0 with h3 | h3 | h3
        · exact Or.inr (Or.inr ⟨by linarith, Or.inr ⟨by linarith,
            Or.inr ⟨by linarith, by linarith⟩⟩⟩)
        · exact absurd (by ext <;> simp [h0, h1, h2, h3]) hq
        · exact Or.inl (Or.inr ⟨h0, Or.inr ⟨h1, Or.inr ⟨h2, h3⟩⟩⟩)
      · exact Or.inl (Or.inr ⟨h0, Or.inr ⟨h1, Or.inl h2⟩⟩)
    · exact Or.inl (Or.inr ⟨h0, Or.inl h1⟩)
  · exact Or.inl (Or.inl h0)

/-- The zero quaternion has no nonzero component, so it is not sign-normalized. -/
theorem not_isSignNormalized_zero : ¬IsSignNormalized (0 : ℍ[ℝ]) := by
  simp [IsSignNormalized]

/-- A positive multiple of a sign-normalized quaternion is sign-normalized. -/
theorem IsSignNormalized.smul {q : ℍ[ℝ]} (h : IsSignNormalized q) {c : ℝ} (hc : 0 < c) :
    IsSignNormalized (c • q) := by
  unfold IsSignNormalized at h ⊢
  simp only [re_smul, imI_smul, imJ_smul, imK_smul, smul_eq_mul]
  rcases h with h | ⟨h0, h | ⟨h1, h | ⟨h2, h⟩⟩⟩
  · exact Or.inl (mul_pos hc h)
  · exact Or.inr ⟨by rw [h0, mul_zero], Or.inl (mul_pos hc h)⟩
  · exact Or.inr ⟨by rw [h0, mul_zero], Or.inr ⟨by rw [h1, mul_zero], Or.inl (mul_pos hc h)⟩⟩
  · exact Or.inr ⟨by rw [h0, mul_zero], Or.inr ⟨by rw [h1, mul_zero],
      Or.inr ⟨by rw [h2, mul_zero], mul_pos hc h⟩⟩⟩

end SympyQuaternion
