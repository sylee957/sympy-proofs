import SympyProofs.LambertW.Complex.Conjugation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An angle parametrization for the upper-half-plane inverse problem

For an input argument `θ ∈ (0, π)`, write the argument of a prospective
preimage as `φ ∈ (0, θ)`. Its imaginary part must be `θ - φ` and its real
part is `(θ - φ) * cos φ / sin φ`. The magnitude of its forward image is
`upperRadius θ φ`. This module proves strict decrease of that scalar function.
-/

namespace LambertW.Complex

open Set

/-- Magnitude equation for an input of argument `θ` and a preimage of argument `φ`. -/
noncomputable def upperRadius (θ φ : ℝ) : ℝ :=
  (θ - φ) / Real.sin φ * Real.exp ((θ - φ) * Real.cos φ / Real.sin φ)

/-- Candidate preimage obtained from the imaginary part of `w + log w`. -/
noncomputable def upperCandidate (θ φ : ℝ) : ℂ :=
  (((θ - φ) * Real.cos φ / Real.sin φ : ℝ) : ℂ) + ((θ - φ : ℝ) : ℂ) * Complex.I

theorem upperRadius_pos {θ φ : ℝ} (hθ : θ < Real.pi) (hφ : φ ∈ Ioo 0 θ) :
    0 < upperRadius θ φ := by
  exact mul_pos (div_pos (sub_pos.mpr hφ.2)
    (Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hθ))) (Real.exp_pos _)

/-- The derivative is negative because its numerator is a sum of squares. -/
theorem hasDerivAt_upperRadius {θ φ : ℝ} (hs : Real.sin φ ≠ 0) :
    HasDerivAt (upperRadius θ)
      (-Real.exp ((θ - φ) * Real.cos φ / Real.sin φ) *
        ((Real.sin φ + (θ - φ) * Real.cos φ) ^ 2 +
          ((θ - φ) * Real.sin φ) ^ 2) / Real.sin φ ^ 3) φ := by
  have ht := (hasDerivAt_const φ θ).sub (hasDerivAt_id φ)
  have hr := ht.div (Real.hasDerivAt_sin φ) hs
  have hu := (ht.mul (Real.hasDerivAt_cos φ)).div (Real.hasDerivAt_sin φ) hs
  convert hr.mul hu.exp using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The magnitude function is strictly decreasing, including the cut argument `π`. -/
theorem strictAntiOn_upperRadius_of_le {θ : ℝ} (hθ : θ ≤ Real.pi) :
    StrictAntiOn (upperRadius θ) (Ioo 0 θ) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 θ)
  · intro φ hφ
    exact (hasDerivAt_upperRadius
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans_le hθ)))).continuousAt.continuousWithinAt
  · intro φ hφ
    have hφ' : φ ∈ Ioo 0 θ := by simpa using hφ
    have hs := Real.sin_pos_of_pos_of_lt_pi hφ'.1 (hφ'.2.trans_le hθ)
    rw [(hasDerivAt_upperRadius (θ := θ) (ne_of_gt hs)).deriv]
    apply div_neg_of_neg_of_pos
    · apply mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
      have hp : 0 < ((θ - φ) * Real.sin φ) ^ 2 :=
        sq_pos_of_pos (mul_pos (sub_pos.mpr hφ'.2) hs)
      positivity
    · positivity

theorem strictAntiOn_upperRadius {θ : ℝ} (hθ : θ < Real.pi) :
    StrictAntiOn (upperRadius θ) (Ioo 0 θ) :=
  strictAntiOn_upperRadius_of_le hθ.le

/-- There is at most one angle parameter for any prescribed magnitude. -/
theorem upperRadius_injOn {θ : ℝ} (hθ : θ < Real.pi) :
    InjOn (upperRadius θ) (Ioo 0 θ) :=
  (strictAntiOn_upperRadius hθ).injOn

@[simp] theorem upperCandidate_re (θ φ : ℝ) :
    (upperCandidate θ φ).re = (θ - φ) * Real.cos φ / Real.sin φ := by
  simp only [upperCandidate, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem upperCandidate_im (θ φ : ℝ) : (upperCandidate θ φ).im = θ - φ := by
  simp only [upperCandidate, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem cos_angle_split (θ φ : ℝ) :
    Real.cos θ = Real.cos φ * Real.cos (θ - φ) - Real.sin φ * Real.sin (θ - φ) := by
  simpa using Real.cos_add φ (θ - φ)

private theorem sin_angle_split (θ φ : ℝ) :
    Real.sin θ = Real.sin φ * Real.cos (θ - φ) + Real.cos φ * Real.sin (θ - φ) := by
  simpa using Real.sin_add φ (θ - φ)

/-- The forward image has the desired real coordinate in polar form. -/
theorem mulExp_upperCandidate_re {θ φ : ℝ} (hs : Real.sin φ ≠ 0) :
    (mulExp (upperCandidate θ φ)).re = upperRadius θ φ * Real.cos θ := by
  rw [mulExp_re, upperCandidate_re, upperCandidate_im, upperRadius, cos_angle_split θ φ]
  field_simp

/-- The forward image has the desired imaginary coordinate in polar form. -/
theorem mulExp_upperCandidate_im {θ φ : ℝ} (hs : Real.sin φ ≠ 0) :
    (mulExp (upperCandidate θ φ)).im = upperRadius θ φ * Real.sin θ := by
  rw [mulExp_im, upperCandidate_re, upperCandidate_im, upperRadius, sin_angle_split θ φ]
  field_simp
  ring

/-- Every admissible angle parameter gives a point in the principal output region. -/
theorem upperCandidate_mem_principalRange {θ φ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (hφ : φ ∈ Ioo 0 θ) :
    upperCandidate θ φ ∈ principalRange := by
  have ht : 0 < θ - φ := sub_pos.mpr hφ.2
  have htπ : θ - φ < Real.pi := by linarith [hθ.2, hφ.1]
  have hsφ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hθ.2)
  have hst := Real.sin_pos_of_pos_of_lt_pi ht htπ
  change (upperCandidate θ φ).im ∈ Ioo (-Real.pi) Real.pi ∧ _
  simp only [upperCandidate_im, upperCandidate_re]
  refine ⟨⟨by linarith [Real.pi_pos], htπ⟩, ?_, ?_⟩
  · intro h
    linarith
  · intro _
    apply (div_lt_div_iff₀ hst hsφ).mpr
    have hp := mul_pos ht (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    rw [sin_angle_split θ φ] at hp
    nlinarith

end LambertW.Complex
