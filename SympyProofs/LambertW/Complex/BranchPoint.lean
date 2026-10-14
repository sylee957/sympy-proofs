import SympyProofs.LambertW.Complex.BoundaryLimits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Continuity at the branch point for both boundary conventions -/

namespace LambertW.Complex

open Set Filter Topology ComplexConjugate

private theorem mul_cos_le_sin {t : ℝ} (ht : t ∈ Icc 0 Real.pi) :
    t * Real.cos t ≤ Real.sin t := by
  have hd (t : ℝ) : HasDerivAt (fun t => Real.sin t - t * Real.cos t)
      (t * Real.sin t) t := by
    convert (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1
    · rfl
    · dsimp; ring
  have hm : MonotoneOn (fun t => Real.sin t - t * Real.cos t) (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 Real.pi := by simpa using ht
      rw [(hd t).deriv]
      exact mul_nonneg ht'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1.le ht'.2.le)
  have h := hm (by simp [Real.pi_pos.le]) ht ht.1
  simpa using h

private theorem neg_one_le_boundary {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    -1 ≤ -t * Real.cos t / Real.sin t := by
  apply (le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)).mpr
  linarith [mul_cos_le_sin ⟨ht.1.le, ht.2.le⟩]

/-- The principal output region lies to the right of the line `re = -1`. -/
theorem neg_one_le_re_of_mem_principalRange {w : ℂ} (hw : w ∈ principalRange) :
    -1 ≤ w.re := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · have hc := (conj_mem_principalRange w).mpr hw
    have ht : -(w.im) ∈ Ioo 0 Real.pi := ⟨by linarith, by linarith [hw.1.1]⟩
    have hb := neg_one_le_boundary ht
    have hg := hc.2.2 (by simpa using ne_of_lt hi)
    simp only [Complex.conj_re, Complex.conj_im] at hg
    exact (hb.trans hg.le)
  · exact (hw.2.1 hi).le
  · exact (neg_one_le_boundary ⟨hi, hw.1.2⟩).trans (hw.2.2 (ne_of_gt hi)).le

theorem neg_one_le_upperCut_re {x : ℝ} (hx : x < -Real.exp (-1)) :
    -1 ≤ (upperCut x).re := by
  have ht : (upperCut x).im ∈ Ioo 0 Real.pi :=
    ⟨upperCut_im_pos hx, upperCut_im_lt_pi hx⟩
  have hz : (mulExp (upperCut x)).im = 0 := by rw [mulExp_upperCut hx]; simp
  rcases (mulExp_im_eq_zero_iff _).mp hz with h | ⟨_, h⟩
  · linarith [ht.1]
  · rw [h]
    exact neg_one_le_boundary ht

/-- The same lower bound holds for either convention, including on the cut. -/
theorem neg_one_le_principalWithBoundary_re (side : BoundarySide) (z : ℂ) :
    -1 ≤ (principalWithBoundary side z).re := by
  by_cases hz : z ∈ principalDomain
  · rw [principalWithBoundary_of_mem side hz]
    exact neg_one_le_re_of_mem_principalRange (principal_mem hz)
  have hr : z.re ≤ -Real.exp (-1) := le_of_not_gt (not_or.mp hz).2
  rcases hr.eq_or_lt with he | he
  · simp [principalWithBoundary, hz, he]
  · cases side <;> simp [principalWithBoundary, hz, ne_of_lt he,
      neg_one_le_upperCut_re he]

/-- The norm is controlled by the input, uniformly across the two conventions. -/
theorem norm_principalWithBoundary_le (side : BoundarySide) (z : ℂ) :
    ‖principalWithBoundary side z‖ ≤ ‖z‖ / Real.exp (-1) := by
  have he := congrArg norm (mulExp_principalWithBoundary side z)
  simp only [mulExp, norm_mul, Complex.norm_exp] at he
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  calc
    ‖principalWithBoundary side z‖ * Real.exp (-1) ≤
        ‖principalWithBoundary side z‖ * Real.exp (principalWithBoundary side z).re :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_one_le_principalWithBoundary_re side z))
        (norm_nonneg _)
    _ = ‖z‖ := he

/-- The critical value has only one preimage in the half-plane `re ≥ -1`. -/
theorem eq_neg_one_of_mulExp_eq_branchPoint {w : ℂ} (hr : -1 ≤ w.re)
    (he : mulExp w = ((-Real.exp (-1) : ℝ) : ℂ)) : w = -1 := by
  have hn : ‖w‖ ≤ 1 := by
    have h := congrArg norm he
    simp only [mulExp, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos (-1))] at h
    have hex := Real.exp_le_exp.mpr hr
    have hle := mul_le_mul_of_nonneg_left hex (norm_nonneg w)
    rw [h] at hle
    nlinarith [Real.exp_pos (-1)]
  have hi : w.im = 0 := by
    have hm : w.re * Real.sin w.im + w.im * Real.cos w.im = 0 := by
      have h := congrArg Complex.im he
      rw [mulExp_im] at h
      simp only [Complex.ofReal_im] at h
      exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
    have hsq : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
      have h := Complex.sq_norm w
      simp only [Complex.normSq_apply] at h
      nlinarith [norm_nonneg w]
    by_contra hi
    have hs := Real.sin_sq_lt_sq hi
    have ht := Real.sin_sq_add_cos_sq w.im
    have heq : (w.re ^ 2 + w.im ^ 2) * Real.sin w.im ^ 2 = w.im ^ 2 := by
      nlinarith [sq_nonneg (w.re * Real.sin w.im - w.im * Real.cos w.im),
        congrArg (fun a : ℝ => a ^ 2) (show w.re * Real.sin w.im = -w.im * Real.cos w.im by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (Real.sin w.im))]
  have hw : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have hf : Real.mulExp w.re = Real.mulExp (-1) := by
    rw [hw, mulExp_ofReal] at he
    rw [Real.mulExp_neg_one]
    exact_mod_cast he
  have hre : w.re = -1 := Real.strictMonoOn_mulExp.injOn hr (by simp) hf
  rw [hw, hre]
  simp

/-- Both choices are continuous at the branch point, even allowing approach
from either side of the cut. -/
theorem continuousAt_principalWithBoundary_branchPoint (side : BoundarySide) :
    ContinuousAt (principalWithBoundary side) ((-Real.exp (-1) : ℝ) : ℂ) := by
  let b : ℂ := ((-Real.exp (-1) : ℝ) : ℂ)
  change Tendsto (principalWithBoundary side) (𝓝 b) (𝓝 (principalWithBoundary side b))
  rw [show principalWithBoundary side b = -1 from principalWithBoundary_branchPoint side]
  apply (isCompact_closedBall (0 : ℂ) ((‖b‖ + 1) / Real.exp (-1))).tendsto_nhds_of_unique_mapClusterPt
  · have hb : ∀ᶠ z in 𝓝 b, ‖z‖ < ‖b‖ + 1 :=
      continuous_norm.continuousAt.tendsto.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hb] with z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_principalWithBoundary_le side z).trans
      (div_le_div_of_nonneg_right hz.le (Real.exp_pos _).le)
  · intro w _ hw
    have hr : -1 ≤ w.re := by
      exact (isClosed_le continuous_const Complex.continuous_re).mem_of_mapClusterPt hw
        (Eventually.of_forall (neg_one_le_principalWithBoundary_re side))
    apply eq_neg_one_of_mulExp_eq_branchPoint hr
    have hc := hw.continuousAt_comp (analyticAt_mulExp w).continuousAt
    have he : mulExp ∘ principalWithBoundary side = id := by
      funext z
      exact mulExp_principalWithBoundary side z
    rw [he, mapClusterPt_id_iff] at hc
    exact eq_of_nhds_neBot hc

end LambertW.Complex
