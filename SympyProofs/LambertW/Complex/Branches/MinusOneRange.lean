import SympyProofs.LambertW.Complex.Branches.MinusOneLog
import Mathlib.Analysis.Complex.RealDeriv

/-! # Exact output region of indexed W₋₁ -/
namespace LambertW.Complex
open Set

/-- The logarithmic inverse equation has at most one solution in the lower half-plane. -/
theorem injOn_add_log_lower : Set.InjOn (fun w : ℂ => w + Complex.log w) {w | w.im < 0} := by
  intro u hu v hv he
  by_contra hne
  have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let d := v - u
  let p : ℂ → ℂ := fun t => u + t * d
  let G : ℂ → ℂ := fun t => ((p t + Complex.log (p t)) / d) * (-Complex.I)
  let g : ℝ → ℝ := fun t => (G t).re
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (p t).im < 0 := by
    dsimp [p, d]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, zero_mul, add_zero]
    change u.im < 0 at hu
    change v.im < 0 at hv
    nlinarith [mul_nonneg ht.1 (le_of_lt (sub_pos.mpr (show 0 > v.im from hv))),
      mul_nonneg (sub_nonneg.mpr ht.2) (le_of_lt (neg_pos.mpr hu))]
  have hg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt g (1 + (p t)⁻¹).im t := by
    have hpd : HasDerivAt p d (t:ℂ) := by
      simpa [p] using ((hasDerivAt_id (t:ℂ)).mul_const d).const_add u
    have h := ((hpd.add ((Complex.hasDerivAt_log (Or.inr (ne_of_lt (hp t ht)))).comp _ hpd)).div_const d).mul_const (-Complex.I)
    have hc : (d + (p t)⁻¹ * d) / d * -Complex.I = (1 + (p t)⁻¹) * -Complex.I := by
      dsimp [d]; field_simp
    rw [hc] at h
    simpa [g, G, Complex.mul_re] using h.real_of_complex
  have hpos (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < (1 + (p t)⁻¹).im := by
    have hpt := hp t ht
    have hn : 0 < Complex.normSq (p t) := Complex.normSq_pos.mpr (by
      intro h; simp [h] at hpt)
    simpa [Complex.inv_im] using div_pos (neg_pos.mpr hpt) hn
  have hm : StrictMonoOn g (Icc (0:ℝ) 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [(hg t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
  have hh := hm (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) (by norm_num : (0:ℝ) < 1)
  have h01 : g 0 = g 1 := by
    dsimp [g, G, p, d]
    simp only [zero_mul, add_zero, one_mul, add_sub_cancel]
    dsimp only at he
    rw [he]
  exact (ne_of_lt hh) h01

private theorem log_mulExp_of_mem_minusOneRange {w : ℂ} (hw : w ∈ minusOneRange) :
    mulExp w ∈ branchDomain ∧
      minusOneLogInput (mulExp w) = w + Complex.log w := by
  let q := w + Complex.log w + 2 * Real.pi * Complex.I
  have hqi : q.im = w.im + Complex.arg w + 2 * Real.pi := by
    simp [q, Complex.mul_im, Complex.log_im]
  have hqlo : -Real.pi < q.im := by rw [hqi]; linarith [hw.2.1]
  have hqhi : q.im < Real.pi := by rw [hqi]; linarith [hw.2.2]
  have hw0 : w ≠ 0 := by intro h; have := hw.1; simp [h] at this
  have he : Complex.exp q = mulExp w := by
    simp only [q, Complex.exp_add, Complex.exp_log hw0, Complex.exp_two_pi_mul_I, mul_one]
    exact mul_comm _ _
  have hl : Complex.log (mulExp w) = q := by
    rw [← he]
    exact Complex.log_exp hqlo hqhi.le
  constructor
  · apply Complex.mem_slitPlane_iff_arg.mpr
    constructor
    · have hh := congrArg Complex.im hl
      rw [Complex.log_im] at hh
      rw [hh]
      exact ne_of_lt hqhi
    · rw [← he]; exact Complex.exp_ne_zero _
  · unfold minusOneLogInput
    rw [hl]
    dsimp [q]
    ring

/-- `mulExp` maps the entire specified curved strip into the slit plane. -/
theorem mapsTo_mulExp_minusOneRange : MapsTo mulExp minusOneRange branchDomain :=
  fun _ hw => (log_mulExp_of_mem_minusOneRange hw).1

/-- The reverse inverse identity on the exact output region. -/
theorem minusOne_mulExp {w : ℂ} (hw : w ∈ minusOneRange) : (branch (-1)) (mulExp w) = w := by
  obtain ⟨hz, he⟩ := log_mulExp_of_mem_minusOneRange hw
  exact injOn_add_log_lower (im_minusOne_neg hz) hw.1 ((minusOne_add_log hz).trans he)

/-- The curved strip is precisely the image of the slit-plane branch. -/
theorem image_minusOne_eq_range : (branch (-1)) '' branchDomain = minusOneRange := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact minusOne_mem_range hz
  · intro w hw
    exact ⟨mulExp w, mapsTo_mulExp_minusOneRange hw, minusOne_mulExp hw⟩

/-- `mulExp` is a bijection from the explicit output region onto the slit plane. -/
theorem bijOn_mulExp_minusOneRange : BijOn mulExp minusOneRange branchDomain := by
  refine ⟨mapsTo_mulExp_minusOneRange, ?_, ?_⟩
  · intro u hu v hv he
    simpa only [minusOne_mulExp hu, minusOne_mulExp hv] using congrArg (branch (-1)) he
  · intro z hz
    exact ⟨(branch (-1)) z, minusOne_mem_range hz, (mulExp_branch (-1)) hz⟩

end LambertW.Complex
