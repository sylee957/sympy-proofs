import SympyProofs.LambertW.Complex.Boundary.Side
import SympyProofs.LambertW.Complex.Principal.Analytic

/-!
# Boundary conventions for the principal Lambert W function

The upper and lower conventions share the analytic inverse on the slit domain.
On the open cut they select conjugate values, and at the branch point both
select `-1`.

This is an internal construction used to prove the public `branchWithBoundary` API.
The one-sided limits are proved in `BoundaryLimits`, and continuity at the
branch point is proved in `BranchPoint`.
-/

namespace LambertW.Complex

open Set Filter Topology ComplexConjugate

/-- The limiting magnitude at the branch point is `exp (-1)`. -/
theorem tendsto_upperRadius_pi_nhdsLT :
    Tendsto (upperRadius Real.pi) (𝓝[<] Real.pi) (𝓝 (Real.exp (-1))) := by
  have ht : Tendsto (fun φ : ℝ => Real.pi - φ) (𝓝[<] Real.pi) (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := Real.pi)).sub
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun φ : ℝ => φ) (𝓝[<] Real.pi) (𝓝 Real.pi)))
  have hs := Real.continuous_sinc.continuousAt.tendsto.comp ht
  have hc := Real.continuous_cos.continuousAt.tendsto.comp ht
  have h : Tendsto (fun φ : ℝ => (Real.sinc (Real.pi - φ))⁻¹ *
      Real.exp (-Real.cos (Real.pi - φ) / Real.sinc (Real.pi - φ)))
      (𝓝[<] Real.pi) (𝓝 (Real.exp (-1))) := by
    simpa only [Real.sinc_zero, Real.cos_zero, inv_one, div_one, one_mul, Function.comp_def, Pi.div_apply] using
      (hs.inv₀ (by simp)).mul (Real.continuous_exp.continuousAt.tendsto.comp
        (hc.neg.div hs (by simp)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with φ hφ
  have hn : Real.pi - φ ≠ 0 := ne_of_gt (sub_pos.mpr hφ.2)
  have hsin : Real.sin (Real.pi - φ) = Real.sin φ := Real.sin_pi_sub φ
  have hcos : Real.cos (Real.pi - φ) = -Real.cos φ := Real.cos_pi_sub φ
  simp only [Real.sinc_of_ne_zero hn, hsin, hcos, neg_neg,
    inv_div, upperRadius, div_div_eq_mul_div]
  congr 2; ring

/-- The magnitude equation has a unique solution on the open cut. -/
theorem existsUnique_upperRadius_pi {r : ℝ} (hr : Real.exp (-1) < r) :
    ∃! φ : ℝ, φ ∈ Ioo 0 Real.pi ∧ upperRadius Real.pi φ = r := by
  have hlo := tendsto_upperRadius_pi_nhdsLT.eventually (eventually_lt_nhds hr)
  have hleft : ∀ᶠ φ in 𝓝[<] Real.pi, φ ∈ Ioo 0 Real.pi :=
    Ioo_mem_nhdsLT Real.pi_pos
  obtain ⟨a, ha, har⟩ := (hleft.and hlo).exists
  have hhi := (tendsto_upperRadius_nhdsGT Real.pi_pos).eventually_ge_atTop r
  have hright : ∀ᶠ φ in 𝓝[>] (0 : ℝ), φ ∈ Ioo 0 Real.pi :=
    Ioo_mem_nhdsGT Real.pi_pos
  obtain ⟨b, hb, hbr⟩ := (hright.and hhi).exists
  have hc : ContinuousOn (upperRadius Real.pi) (Ioo 0 Real.pi) := by
    intro φ hφ
    exact (hasDerivAt_upperRadius
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2))).continuousAt.continuousWithinAt
  obtain ⟨φ, hφ, he⟩ := isPreconnected_Ioo.intermediate_value ha hb hc ⟨har.le, hbr⟩
  refine ⟨φ, ⟨hφ, he⟩, fun ψ hψ => ?_⟩
  exact (strictAntiOn_upperRadius_of_le le_rfl).injOn hψ.1 hφ (hψ.2.trans he.symm)

/-- Angle used to select the upper boundary value; specified for `x < -exp (-1)`. -/
noncomputable def cutAngle (x : ℝ) : ℝ :=
  Function.invFunOn (upperRadius Real.pi) (Ioo 0 Real.pi) (-x)

theorem cutAngle_mem {x : ℝ} (hx : x < -Real.exp (-1)) :
    cutAngle x ∈ Ioo 0 Real.pi :=
  Function.invFunOn_mem (existsUnique_upperRadius_pi (by linarith : Real.exp (-1) < -x)).exists

theorem upperRadius_cutAngle {x : ℝ} (hx : x < -Real.exp (-1)) :
    upperRadius Real.pi (cutAngle x) = -x :=
  Function.invFunOn_eq (existsUnique_upperRadius_pi (by linarith : Real.exp (-1) < -x)).exists

/-- Upper boundary value on the open cut. -/
noncomputable def upperCut (x : ℝ) : ℂ := upperCandidate Real.pi (cutAngle x)

theorem upperCut_im_pos {x : ℝ} (hx : x < -Real.exp (-1)) :
    0 < (upperCut x).im := by
  simpa [upperCut] using sub_pos.mpr (cutAngle_mem hx).2

theorem upperCut_im_lt_pi {x : ℝ} (hx : x < -Real.exp (-1)) :
    (upperCut x).im < Real.pi := by
  simp only [upperCut, upperCandidate_im]
  linarith [(cutAngle_mem hx).1]

theorem mulExp_upperCut {x : ℝ} (hx : x < -Real.exp (-1)) :
    mulExp (upperCut x) = (x : ℂ) := by
  have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (cutAngle_mem hx).1 (cutAngle_mem hx).2)
  apply Complex.ext
  · simp [upperCut, mulExp_upperCandidate_re hs, upperRadius_cutAngle hx]
  · simp [upperCut, mulExp_upperCandidate_im hs]

/-- Principal inverse with an explicit boundary convention. -/
noncomputable def BoundaryInternal.principalModel (side : BoundarySide) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ principalDomain then principal z
    else if z.re = -Real.exp (-1) then -1
    else match side with
      | .upper => upperCut z.re
      | .lower => conj (upperCut z.re)

@[simp] theorem BoundaryInternal.principalModel_of_mem (side : BoundarySide) {z : ℂ}
    (hz : z ∈ principalDomain) : BoundaryInternal.principalModel side z = principal z := by
  simp [BoundaryInternal.principalModel, hz]

@[simp] theorem BoundaryInternal.principalModel_branchPoint (side : BoundarySide) :
    BoundaryInternal.principalModel side ((-Real.exp (-1) : ℝ) : ℂ) = -1 := by
  simp only [BoundaryInternal.principalModel, ofReal_mem_principalDomain, lt_self_iff_false,
    Complex.ofReal_re, ↓reduceIte]

theorem BoundaryInternal.principalModel_upper_cut {x : ℝ} (hx : x < -Real.exp (-1)) :
    BoundaryInternal.principalModel .upper (x : ℂ) = upperCut x := by
  simp [BoundaryInternal.principalModel, principalDomain, not_lt.mpr hx.le, ne_of_lt hx]

theorem BoundaryInternal.principalModel_lower_cut {x : ℝ} (hx : x < -Real.exp (-1)) :
    BoundaryInternal.principalModel .lower (x : ℂ) = conj (upperCut x) := by
  simp [BoundaryInternal.principalModel, principalDomain, not_lt.mpr hx.le, ne_of_lt hx]

/-- The defining equation holds everywhere, including the cut and its endpoint. -/
theorem BoundaryInternal.mulExp_principalModel (side : BoundarySide) (z : ℂ) :
    mulExp (BoundaryInternal.principalModel side z) = z := by
  by_cases hz : z ∈ principalDomain
  · rw [BoundaryInternal.principalModel_of_mem side hz]
    exact mulExp_principal hz
  have hi : z.im = 0 := by simpa [principalDomain] using (not_or.mp hz).1
  have hr : z.re ≤ -Real.exp (-1) := le_of_not_gt (not_or.mp hz).2
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  rw [he]
  rcases hr.eq_or_lt with hr | hr
  · rw [hr, BoundaryInternal.principalModel_branchPoint]
    simp [mulExp_neg_one, Complex.ofReal_exp]
  · cases side with
    | upper => rw [BoundaryInternal.principalModel_upper_cut hr, mulExp_upperCut hr]
    | lower => rw [BoundaryInternal.principalModel_lower_cut hr, mulExp_conj, mulExp_upperCut hr]; simp

/-- Conjugation switches the convention, on and off the cut. -/
theorem BoundaryInternal.principalModel_conj (side : BoundarySide) (z : ℂ) :
    BoundaryInternal.principalModel side.opposite (conj z) = conj (BoundaryInternal.principalModel side z) := by
  by_cases hz : z ∈ principalDomain
  · rw [BoundaryInternal.principalModel_of_mem _ ((conj_mem_principalDomain z).mpr hz),
      BoundaryInternal.principalModel_of_mem _ hz, principal_conj hz]
  · have hc : conj z ∉ principalDomain := by simpa using hz
    by_cases he : z.re = -Real.exp (-1) <;>
      cases side <;> simp [BoundaryInternal.principalModel, hz, hc, he, BoundarySide.opposite]

/-- The conventions give different values precisely on the open cut. -/
theorem BoundaryInternal.principalModel_upper_ne_lower {x : ℝ} (hx : x < -Real.exp (-1)) :
    BoundaryInternal.principalModel .upper (x : ℂ) ≠ BoundaryInternal.principalModel .lower (x : ℂ) := by
  rw [BoundaryInternal.principalModel_upper_cut hx, BoundaryInternal.principalModel_lower_cut hx]
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith [upperCut_im_pos hx]

/-- Agreement with the real branch includes the branch point, for either convention. -/
theorem BoundaryInternal.principalModel_ofReal (side : BoundarySide) {x : ℝ}
    (hx : -Real.exp (-1) ≤ x) :
    BoundaryInternal.principalModel side (x : ℂ) = (Real.principal x : ℂ) := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, BoundaryInternal.principalModel_branchPoint, Real.principal_neg_exp_neg_one]
    simp
  · rw [BoundaryInternal.principalModel_of_mem _ ((ofReal_mem_principalDomain x).mpr h),
      principal_ofReal h]

@[simp] theorem BoundaryInternal.principalModel_zero (side : BoundarySide) :
    BoundaryInternal.principalModel side 0 = 0 := by
  rw [BoundaryInternal.principalModel_of_mem _ zero_mem_principalDomain, principal_zero]

/-- Adding boundary values preserves analyticity at every point of the slit domain. -/
theorem BoundaryInternal.analyticAt_principalModel (side : BoundarySide) {z : ℂ}
    (hz : z ∈ principalDomain) : AnalyticAt ℂ (BoundaryInternal.principalModel side) z := by
  apply (analyticAt_principal hz).congr
  filter_upwards [isOpen_principalDomain.mem_nhds hz] with y hy
  exact (BoundaryInternal.principalModel_of_mem side hy).symm

end LambertW.Complex
