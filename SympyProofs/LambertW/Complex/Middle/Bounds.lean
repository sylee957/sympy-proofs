import SympyProofs.LambertW.Complex.Middle.LocalPathLifting

/-!
# Bounds for continuing inverse branches

For a large inverse value `w`, the factor `w / (1+w)` is bounded by two.
Consequently inverse derivatives are uniformly bounded while the input stays
away from zero. These are estimates for path continuation, not a global
path-lifting theorem.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- Large values stay quantitatively away from the critical point. -/
theorem norm_one_add_ge_half {w : ℂ} (hw : 2 ≤ ‖w‖) :
    ‖w‖ / 2 ≤ ‖1 + w‖ := by
  have h := norm_sub_le (1 + w) (1 : ℂ)
  have he : 1 + w - 1 = w := by ring
  rw [he, norm_one] at h
  linarith

/-- The logarithmic inverse-derivative factor is bounded at large values. -/
theorem norm_div_one_add_le_two {w : ℂ} (hw : 2 ≤ ‖w‖) :
    ‖w / (1 + w)‖ ≤ 2 := by
  have hh := norm_one_add_ge_half hw
  have hp : 0 < ‖1 + w‖ := by linarith
  rw [norm_div]
  apply (div_le_iff₀ hp).mpr
  linarith

/-- At a large inverse value, the derivative is bounded by `2 / ‖z‖`. -/
theorem norm_inverse_derivative_le {w z : ℂ} (hw : 2 ≤ ‖w‖)
    (hz : mulExp w = z) :
    ‖(Complex.exp w * (1 + w))⁻¹‖ ≤ 2 / ‖z‖ := by
  have hwp : 0 < ‖w‖ := by linarith
  have hwn : w ≠ 0 := norm_pos_iff.mp hwp
  have hzn : z ≠ 0 := by
    rw [← hz, mulExp]
    exact mul_ne_zero hwn (Complex.exp_ne_zero _)
  have he : (Complex.exp w * (1 + w))⁻¹ = (w / (1 + w)) / z := by
    rw [← hz, mulExp]
    field_simp
  rw [he, norm_div]
  exact div_le_div_of_nonneg_right (norm_div_one_add_le_two hw) (norm_nonneg z)

/-- A uniform bound when the input has a positive distance from zero. -/
theorem norm_inverse_derivative_le_of_norm_ge {w z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hzδ : δ ≤ ‖z‖) (hw : 2 ≤ ‖w‖) (hz : mulExp w = z) :
    ‖(Complex.exp w * (1 + w))⁻¹‖ ≤ 2 / δ := by
  exact (norm_inverse_derivative_le hw hz).trans
    (div_le_div_of_nonneg_left (by norm_num) hδ hzδ)

/-- Any differentiable inverse has the inverse-derivative formula, wherever
its right-inverse identity holds locally. -/
theorem deriv_of_eventually_mulExp_eq {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z)
    (hi : ∀ᶠ y in 𝓝 z, mulExp (F y) = y) :
    deriv F z = (Complex.exp (F z) * (1 + F z))⁻¹ := by
  have hc := (hasDerivAt_mulExp (F z)).comp z hF.hasDerivAt
  have hid := (hasDerivAt_id z).congr_of_eventuallyEq hi
  have he := hc.unique hid
  have hn : Complex.exp (F z) * (1 + F z) ≠ 0 := by
    intro hn
    rw [hn, zero_mul] at he
    exact zero_ne_one he
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using he

/-- The uniform bound applies to every differentiable local inverse, without
assuming any particular branch index. -/
theorem norm_deriv_inverse_le {F : ℂ → ℂ} {z : ℂ} {δ : ℝ}
    (hF : DifferentiableAt ℂ F z)
    (hi : ∀ᶠ y in 𝓝 z, mulExp (F y) = y)
    (hδ : 0 < δ) (hzδ : δ ≤ ‖z‖) (hw : 2 ≤ ‖F z‖) :
    ‖deriv F z‖ ≤ 2 / δ := by
  rw [deriv_of_eventually_mulExp_eq hF hi]
  exact norm_inverse_derivative_le_of_norm_ge hδ hzδ hw hi.self_of_nhds

/-- Large lifted values cannot move faster than `2/δ` times the input speed
while the input stays at distance at least `δ` from zero. -/
theorem norm_path_lift_derivative_le {F γ : ℝ → ℂ} {t : ℝ} {v u : ℂ} {δ : ℝ}
    (hF : HasDerivAt F v t) (hγ : HasDerivAt γ u t)
    (hi : ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hδ : 0 < δ) (hγδ : δ ≤ ‖γ t‖) (hw : 2 ≤ ‖F t‖) :
    ‖v‖ ≤ (2 / δ) * ‖u‖ := by
  have hc := (hasDerivAt_mulExp (F t)).comp t hF
  have he := hc.unique (hγ.congr_of_eventuallyEq hi)
  have hp : 0 < ‖1 + F t‖ := by
    have hh := norm_one_add_ge_half hw
    linarith
  have hn : Complex.exp (F t) * (1 + F t) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (norm_pos_iff.mp hp)
  have hv : v = (Complex.exp (F t) * (1 + F t))⁻¹ * u := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [hv, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_inverse_derivative_le_of_norm_ge hδ hγδ hw hi.self_of_nhds) (norm_nonneg u)

end LambertW.Complex
