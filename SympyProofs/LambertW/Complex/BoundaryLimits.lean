import SympyProofs.LambertW.Complex.Boundary

/-! # One-sided limits of the principal branch on the open cut -/

namespace LambertW.Complex

open Set Filter Topology ComplexConjugate

/-- Near a point on the open cut, the upper value has an analytic inverse germ
which agrees with `principal` on the upper half-plane. -/
theorem exists_analytic_upperCut_inverse {x : ℝ} (hx : x < -Real.exp (-1)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (x : ℂ) ∧ g x = upperCut x ∧
      ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → principal z = g z := by
  let w := upperCut x
  have he : mulExp w = (x : ℂ) := mulExp_upperCut hx
  have hn : deriv mulExp w ≠ 0 := by
    apply deriv_mulExp_ne_zero
    intro h
    have hp := upperCut_im_pos hx
    change 0 < w.im at hp
    simp [h] at hp
  have ha := analyticAt_mulExp w
  let g := ha.hasStrictDerivAt.localInverse mulExp (deriv mulExp w) w hn
  have hg : AnalyticAt ℂ g (x : ℂ) := by
    simpa [g, he] using ha.analyticAt_localInverse hn
  have hgw : g x = w := by
    simpa [g, he] using (ha.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hinv : ∀ᶠ z in 𝓝 (x : ℂ), mulExp (g z) = z := by
    simpa [g, he] using ha.hasStrictDerivAt.eventually_right_inverse hn
  have him : ∀ᶠ z in 𝓝 (x : ℂ), (g z).im ∈ Ioo 0 Real.pi := by
    have hc := Complex.continuous_im.continuousAt.comp hg.continuousAt
    apply hc.tendsto.eventually
    apply isOpen_Ioo.mem_nhds
    simpa [hgw, w] using And.intro (upperCut_im_pos hx) (upperCut_im_lt_pi hx)
  refine ⟨g, hg, hgw, ?_⟩
  filter_upwards [hinv, him] with z hi hm hz
  apply (eq_principal_of_mulExp_eq (w := g z) ?_ hi).symm
  have hs := Real.sin_pos_of_pos_of_lt_pi hm.1 hm.2
  have hp : 0 < (g z).re * Real.sin (g z).im + (g z).im * Real.cos (g z).im := by
    have hh : 0 < (mulExp (g z)).im := by simpa [hi] using hz
    rw [mulExp_im] at hh
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hh
  refine ⟨⟨by linarith [Real.pi_pos, hm.1], hm.2⟩, ?_, ?_⟩
  · intro h
    linarith [hm.1]
  · intro _
    apply (div_lt_iff₀ hs).mpr
    linarith

/-- The chosen upper cut value is the limit from the complex upper half-plane. -/
theorem tendsto_principal_upperCut {x : ℝ} (hx : x < -Real.exp (-1)) :
    Tendsto principal (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (upperCut x)) := by
  obtain ⟨g, hg, he, hagree⟩ := exists_analytic_upperCut_inverse hx
  have ht : Tendsto g (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (upperCut x)) := by
    simpa [he] using hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [hagree.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hi
  exact (hz hi).symm

/-- The lower limit is the conjugate of the upper limit. -/
theorem tendsto_principal_lowerCut {x : ℝ} (hx : x < -Real.exp (-1)) :
    Tendsto principal (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (conj (upperCut x))) := by
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h := Complex.continuous_conj.tendsto (x : ℂ)
      simpa using h.mono_left (nhdsWithin_le_nhds :
        𝓝[{z : ℂ | z.im < 0}] (x : ℂ) ≤ 𝓝 (x : ℂ))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have ht := Complex.continuous_conj.continuousAt.tendsto.comp
    ((tendsto_principal_upperCut hx).comp hc)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hd : z ∈ principalDomain := Or.inl (ne_of_lt hz)
  simp [Function.comp_def, principal_conj hd]

/-- Boundary choice selects exactly the corresponding one-sided limit on the open cut. -/
theorem tendsto_principalWithBoundary_cut (side : BoundarySide) {x : ℝ}
    (hx : x < -Real.exp (-1)) :
    Tendsto (principalWithBoundary side)
      (𝓝[{z : ℂ | match side with
        | .upper => 0 < z.im
        | .lower => z.im < 0}] (x : ℂ))
      (𝓝 (principalWithBoundary side (x : ℂ))) := by
  cases side with
  | upper =>
    rw [principalWithBoundary_upper_cut hx]
    apply (tendsto_principal_upperCut hx).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (principalWithBoundary_of_mem _ (Or.inl (ne_of_gt hz))).symm
  | lower =>
    rw [principalWithBoundary_lower_cut hx]
    apply (tendsto_principal_lowerCut hx).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (principalWithBoundary_of_mem _ (Or.inl (ne_of_lt hz))).symm

end LambertW.Complex
