import SympyProofs.LambertW.Complex.Principal.UpperExistence

/-! # Uniqueness of the principal complex inverse -/

namespace LambertW.Complex

open Set

private theorem arg_mem_Ioo_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    w.arg ∈ Ioo 0 Real.pi := by
  refine ⟨?_, Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hw))⟩
  have hn := Complex.arg_nonneg_iff.mpr hw.le
  by_contra h
  have he : w.arg = 0 := le_antisymm (not_lt.mp h) hn
  have hs := Complex.norm_mul_sin_arg w
  simp [he] at hs
  linarith

private theorem mulExp_polar (w : ℂ) :
    mulExp w = ((‖w‖ * Real.exp w.re : ℝ) : ℂ) *
      ((Real.cos (w.arg + w.im) : ℂ) + (Real.sin (w.arg + w.im) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [mulExp_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, sub_zero]
    simp only [Real.cos_add]
    linear_combination
      -Real.exp w.re * Real.cos w.im * Complex.norm_mul_cos_arg w +
      Real.exp w.re * Real.sin w.im * Complex.norm_mul_sin_arg w
  · simp only [mulExp_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, add_zero]
    simp only [Real.sin_add]
    linear_combination
      -Real.exp w.re * Real.sin w.im * Complex.norm_mul_cos_arg w -
      Real.exp w.re * Real.cos w.im * Complex.norm_mul_sin_arg w

/-- In the upper principal region no wrapping occurs in the forward-map argument. -/
theorem arg_mulExp_of_mem_principalRange {w : ℂ}
    (hw : w ∈ principalRange) (hi : 0 < w.im) :
    (mulExp w).arg = w.arg + w.im := by
  have ha := arg_mem_Ioo_of_im_pos hi
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (by intro h; simp [h] at hi)
  have hp := mulExp_im_pos_of_mem_principalRange hw hi
  have hs : 0 < Real.sin (w.arg + w.im) := by
    have he := congrArg Complex.im (mulExp_polar w)
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at he
    have hc : 0 < ‖w‖ * Real.exp w.re := mul_pos hn (Real.exp_pos _)
    nlinarith
  have hsum : w.arg + w.im < Real.pi := by
    by_contra h
    have ht : 0 ≤ w.arg + w.im - Real.pi := by linarith
    have ht' : w.arg + w.im - Real.pi ≤ Real.pi := by linarith [hw.1.2, ha.2]
    have hh := Real.sin_nonneg_of_nonneg_of_le_pi ht ht'
    simp only [Real.sin_sub, Real.sin_pi, Real.cos_pi] at hh
    linarith
  rw [mulExp_polar]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I (mul_pos hn (Real.exp_pos w.re))
      (show w.arg + w.im ∈ Ioc (-Real.pi) Real.pi from
        ⟨by linarith [Real.pi_pos, ha.1], hsum.le⟩)

/-- Every upper-half-plane principal solution has the angle parametrization. -/
theorem principal_solution_upperCandidate {w z : ℂ}
    (hw : w ∈ principalRange) (he : mulExp w = z) (hz : 0 < z.im) :
    w.arg ∈ Ioo 0 z.arg ∧ w = upperCandidate z.arg w.arg ∧
      upperRadius z.arg w.arg = ‖z‖ := by
  have hi := im_pos_of_principal_solution hw he hz
  have ha := arg_mem_Ioo_of_im_pos hi
  have haz := arg_mem_Ioo_of_im_pos hz
  have hearg : z.arg = w.arg + w.im := by
    rw [← he]
    exact arg_mulExp_of_mem_principalRange hw hi
  have ht : z.arg - w.arg = w.im := by linarith
  have hs : Real.sin w.arg ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2)
  have hc : w = upperCandidate z.arg w.arg := by
    apply Complex.ext
    · rw [upperCandidate_re, ht]
      apply (eq_div_iff hs).mpr
      have hcos := Complex.norm_mul_cos_arg w
      have hsin := Complex.norm_mul_sin_arg w
      rw [← hcos, ← hsin]
      ring
    · rw [upperCandidate_im, ht]
  refine ⟨⟨ha.1, by linarith⟩, hc, ?_⟩
  have him := mulExp_upperCandidate_im (θ := z.arg) hs
  rw [← hc, he] at him
  have hnorm := Complex.norm_mul_sin_arg z
  have hp := Real.sin_pos_of_pos_of_lt_pi haz.1 haz.2
  nlinarith

/-- Unique solvability in the upper half-plane. -/
theorem existsUnique_principalRange_mulExp_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z := by
  obtain ⟨w, hw, he⟩ := exists_principalRange_mulExp_of_im_pos hz
  refine ⟨w, ⟨hw, he⟩, ?_⟩
  intro v hv
  obtain ⟨hva, hvc, hvr⟩ := principal_solution_upperCandidate hv.1 hv.2 hz
  obtain ⟨hwa, hwc, hwr⟩ := principal_solution_upperCandidate hw he hz
  have ha := upperRadius_injOn (arg_mem_Ioo_of_im_pos hz).2 hva hwa (hvr.trans hwr.symm)
  rw [hvc, hwc, ha]

/-- Every input in the principal slit domain has exactly one principal-region preimage. -/
theorem existsUnique_principalRange_mulExp {z : ℂ} (hz : z ∈ principalDomain) :
    ∃! w : ℂ, w ∈ principalRange ∧ mulExp w = z :=
  existsUnique_principalRange_mulExp_of_upper
    (fun _ hz => existsUnique_principalRange_mulExp_of_im_pos hz) hz

/-- The forward map is a bijection between the principal range and slit domain. -/
theorem mulExp_bijOn_principalDomain : BijOn mulExp principalRange principalDomain := by
  refine ⟨mulExp_mapsTo_principalDomain, ?_, mulExp_surjOn_principalDomain⟩
  intro w hw v hv he
  exact (existsUnique_principalRange_mulExp (mulExp_mapsTo_principalDomain hw)).unique
    ⟨hw, rfl⟩ ⟨hv, he.symm⟩

end LambertW.Complex
