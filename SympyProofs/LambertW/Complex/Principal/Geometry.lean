import SympyProofs.LambertW.Complex.Principal.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Geometry of the principal complex Lambert W branch

The principal slit domain excludes the real ray `(-∞, -exp (-1)]`.
The preimage of the real axis under `mulExp` consists of the real axis and
quadratrix arcs. These are geometric prerequisites for a global inverse;
this module does not yet assert global existence or injectivity.
-/

namespace LambertW.Complex

open Set

/-- The open principal slit domain, excluding the branch point itself. -/
def principalDomain : Set ℂ := {z | z.im ≠ 0 ∨ -Real.exp (-1) < z.re}

theorem isOpen_principalDomain : IsOpen principalDomain := by
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_lt continuous_const Complex.continuous_re)

@[simp] theorem zero_mem_principalDomain : (0 : ℂ) ∈ principalDomain := by
  simp [principalDomain, Real.exp_pos]

@[simp] theorem ofReal_mem_principalDomain (x : ℝ) :
    (x : ℂ) ∈ principalDomain ↔ -Real.exp (-1) < x := by
  simp [principalDomain]

theorem criticalValue_notMem_principalDomain :
    mulExp (-1) ∉ principalDomain := by
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, mulExp_ofReal,
    ofReal_mem_principalDomain, Real.mulExp_neg_one]
  exact lt_irrefl _

/-- Every preimage of a point in the principal slit domain is noncritical. -/
theorem deriv_mulExp_ne_zero_of_mem_principalDomain {w : ℂ}
    (hw : mulExp w ∈ principalDomain) : deriv mulExp w ≠ 0 := by
  apply deriv_mulExp_ne_zero
  intro h
  subst w
  exact criticalValue_notMem_principalDomain hw

theorem mulExp_re (w : ℂ) :
    (mulExp w).re = Real.exp w.re *
      (w.re * Real.cos w.im - w.im * Real.sin w.im) := by
  simp only [mulExp, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  ring

theorem mulExp_im (w : ℂ) :
    (mulExp w).im = Real.exp w.re *
      (w.re * Real.sin w.im + w.im * Real.cos w.im) := by
  simp only [mulExp, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  ring

/-- The full preimage of the real axis, with the zero-sine case handled separately. -/
theorem mulExp_im_eq_zero_iff (w : ℂ) :
    (mulExp w).im = 0 ↔ w.im = 0 ∨
      (Real.sin w.im ≠ 0 ∧ w.re = -w.im * Real.cos w.im / Real.sin w.im) := by
  rw [mulExp_im, mul_eq_zero]
  simp only [Real.exp_ne_zero, false_or]
  constructor
  · intro h
    by_cases hs : Real.sin w.im = 0
    · left
      have hc : Real.cos w.im ≠ 0 := by
        intro hc
        have := Real.sin_sq_add_cos_sq w.im
        simp [hs, hc] at this
      simpa [hs, hc] using h
    · right
      refine ⟨hs, (eq_div_iff hs).mpr ?_⟩
      nlinarith
  · rintro (h | ⟨hs, h⟩)
    · simp [h]
    · have := (eq_div_iff hs).mp h
      nlinarith

/-- A quadratrix parametrization. Geometric claims require `sin t ≠ 0`. -/
noncomputable def quadratrix (t : ℝ) : ℂ :=
  ((-t * Real.cos t / Real.sin t : ℝ) : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem quadratrix_re (t : ℝ) :
    (quadratrix t).re = -t * Real.cos t / Real.sin t := by
  simp only [quadratrix, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem quadratrix_im (t : ℝ) : (quadratrix t).im = t := by
  simp only [quadratrix, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem mulExp_quadratrix_im {t : ℝ} (ht : Real.sin t ≠ 0) :
    (mulExp (quadratrix t)).im = 0 := by
  apply (mulExp_im_eq_zero_iff _).mpr
  right
  simpa using And.intro ht (rfl : -t * Real.cos t / Real.sin t = _)

/-- The real coordinate of the image of a quadratrix arc. -/
theorem mulExp_quadratrix_re {t : ℝ} (ht : Real.sin t ≠ 0) :
    (mulExp (quadratrix t)).re =
      -(t / Real.sin t) * Real.exp (-t * Real.cos t / Real.sin t) := by
  rw [mulExp_re, quadratrix_re, quadratrix_im]
  have htrig := Real.sin_sq_add_cos_sq t
  field_simp
  linear_combination -t * htrig

end LambertW.Complex
