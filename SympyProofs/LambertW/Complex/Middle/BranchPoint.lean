import SympyProofs.LambertW.Complex.Middle.Real
import SympyProofs.LambertW.Complex.Principal.SquareRoot

/-! # The middle branch at the real branch point

The middle branch tends to `-1` from below at `-exp (-1)`. Its displacement
has the negative square-root asymptotic, in contrast to the principal branch.
-/

open Set Filter Topology

namespace LambertW.Real

/-- The lower branch extends continuously to the branch point from the right. -/
theorem tendsto_lower_nhdsGT_branchPoint :
    Tendsto lower (𝓝[>] (-Real.exp (-1))) (𝓝 (-1)) := by
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  have hc : Tendsto (fun x : ℝ => (x : EReal)) (𝓝[>] (-Real.exp (-1)))
      (𝓝[Icc ((-Real.exp (-1) : ℝ) : EReal) 0] ((-Real.exp (-1) : ℝ) : EReal)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_coe_real_ereal.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hx0
    constructor
    · exact_mod_cast (le_of_lt (show -Real.exp (-1) < x from hx))
    · exact_mod_cast hx0.le
  have hm : ((-Real.exp (-1) : ℝ) : EReal) ∈
      Icc ((-Real.exp (-1) : ℝ) : EReal) 0 := ⟨le_rfl, by exact_mod_cast hb.le⟩
  have h := (EReal.continuousOn_lower _ hm).tendsto.comp hc
  rw [EReal.lower_neg_exp_neg_one] at h
  apply EReal.tendsto_coe.mp
  apply h.congr'
  filter_upwards [(eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx
  exact EReal.lower_coe (ne_of_lt hx)

end LambertW.Real

namespace LambertW.Complex

/-- The squared middle displacement has the same leading coefficient as the principal branch. -/
theorem tendsto_real_lower_sq_div :
    Tendsto (fun x : ℝ => ((Real.lower x : ℂ) + 1) ^ 2 /
      ((x + Real.exp (-1) : ℝ) : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (2 * Complex.exp 1)) := by
  obtain ⟨g, hg, hg0, he⟩ := exists_mulExp_branchPoint_factor
  have hw : Tendsto (fun x : ℝ => (Real.lower x : ℂ) + 1)
      (𝓝[>] (-Real.exp (-1))) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_lower_nhdsGT_branchPoint
    simpa using h.add_const 1
  have ht := (hg.continuousAt.tendsto.comp hw).inv₀
    (by rw [hg0]; exact div_ne_zero (Complex.exp_ne_zero _) (by norm_num))
  have hc : (g 0)⁻¹ = 2 * Complex.exp 1 := by
    rw [hg0, inv_div, Complex.exp_neg]
    simp [div_eq_mul_inv]
  rw [hc] at ht
  apply ht.congr'
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hx0
  change -Real.exp (-1) < x at hx
  have h : ((x + Real.exp (-1) : ℝ) : ℂ) =
      ((Real.lower x : ℂ) + 1) ^ 2 * g ((Real.lower x : ℂ) + 1) := by
    have hh := he ((Real.lower x : ℂ) + 1)
    simpa only [add_sub_cancel_right, mulExp_ofReal,
      Real.mulExp_lower ⟨hx.le, hx0⟩, mulExp_neg_one,
      Complex.ofReal_neg, Complex.ofReal_exp, Complex.ofReal_one, sub_neg_eq_add,
      Complex.ofReal_add] using hh
  have hu : (Real.lower x : ℂ) + 1 ≠ 0 := by
    intro hu
    rw [hu, zero_pow (by decide), zero_mul] at h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at hr
    linarith
  rw [h]
  dsimp only [Function.comp_def]
  field_simp

/-- On the real lower branch the negative square root is selected. -/
theorem tendsto_real_lower_div_sqrt :
    Tendsto (fun x : ℝ => (Real.lower x + 1) / Real.sqrt (x + Real.exp (-1)))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (-Real.sqrt (2 * Real.exp 1))) := by
  have h := (Real.continuous_sqrt.continuousAt.tendsto.comp
    tendsto_real_lower_sq_div.norm).neg
  simp only [Function.comp_def, norm_div, norm_pow, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), norm_mul, Complex.norm_exp, Complex.one_re,
    Complex.norm_ofNat] at h
  apply h.congr'
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hx0
  change -Real.exp (-1) < x at hx
  have hl : Real.lower x + 1 ≤ 0 := by
    have hh := Real.lower_mem ⟨hx.le, hx0⟩
    change Real.lower x ≤ -1 at hh
    linarith
  have hd : 0 ≤ x + Real.exp (-1) := by linarith
  rw [← Complex.ofReal_one, ← Complex.ofReal_add]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hl, abs_of_nonneg hd]
  ring

end LambertW.Complex
