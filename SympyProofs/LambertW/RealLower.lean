import SympyProofs.LambertW.RealPrincipal

/-!
# The lower real branch of Lambert W

The map `w ↦ w * exp w` is strictly decreasing on `(-∞, -1]` with image
`[-exp (-1), 0)`. Its inverse on these intervals is `lower`, whose value
outside this input domain is unspecified. This module also compares the
lower and principal branches.
-/

namespace LambertW.Real

open Set

theorem strictAntiOn_mulExp : StrictAntiOn mulExp (Iic (-1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic (-1)) continuous_mulExp.continuousOn
  intro w hw
  rw [(hasDerivAt_mulExp w).deriv]
  have hw' : w < -1 := by simpa using hw
  exact mul_neg_of_pos_of_neg (Real.exp_pos w) (by linarith)

theorem tendsto_mulExp_atBot : Filter.Tendsto mulExp Filter.atBot (nhds 0) := by
  change Filter.Tendsto (fun w : ℝ => w * Real.exp w) Filter.atBot (nhds 0)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    Filter.tendsto_neg_atBot_atTop
  simpa [mulExp, Function.comp_def] using h.neg

/-- The lower branch cannot take the input zero: its forward map is strictly negative. -/
theorem mulExp_neg_of_le_neg_one {w : ℝ} (hw : w ≤ -1) : mulExp w < 0 := by
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)

/-- Existence on the lower branch follows from the limit at `-∞` and the IVT. -/
theorem exists_lower_mulExp_eq {x : ℝ} (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    ∃ w ∈ Iic (-1 : ℝ), mulExp w = x := by
  have hgt : ∀ᶠ w in Filter.atBot, x < mulExp w :=
    tendsto_mulExp_atBot.eventually (eventually_gt_nhds hx.2)
  obtain ⟨a, ha, hax⟩ := ((Filter.eventually_le_atBot (-1 : ℝ)).and hgt).exists
  obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc' ha
    continuous_mulExp.continuousOn ⟨by simpa using hx.1, hax.le⟩
  exact ⟨w, hw.2, hwe⟩

theorem existsUnique_lower_mulExp_eq {x : ℝ} (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    ∃! w : ℝ, w ∈ Iic (-1 : ℝ) ∧ mulExp w = x := by
  obtain ⟨w, hw, hwe⟩ := exists_lower_mulExp_eq hx
  refine ⟨w, ⟨hw, hwe⟩, ?_⟩
  intro v hv
  exact strictAntiOn_mulExp.injOn hv.1 hw (hv.2.trans hwe.symm)

/-- The lower real branch `W₋₁`, specified for `-exp (-1) ≤ x < 0`.
In particular, this definition does not specify a meaningful value at zero. -/
noncomputable def lower : ℝ → ℝ :=
  Function.invFunOn mulExp (Iic (-1))

theorem lower_mem {x : ℝ} (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    lower x ∈ Iic (-1 : ℝ) :=
  Function.invFunOn_mem (exists_lower_mulExp_eq hx)

theorem mulExp_lower {x : ℝ} (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    mulExp (lower x) = x :=
  Function.invFunOn_eq (exists_lower_mulExp_eq hx)

theorem lower_mul_exp {x : ℝ} (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    lower x * Real.exp (lower x) = x :=
  mulExp_lower hx

theorem lower_mulExp {w : ℝ} (hw : w ≤ -1) : lower (mulExp w) = w := by
  exact strictAntiOn_mulExp.injOn (Function.invFunOn_apply_mem hw) hw
    (Function.invFunOn_apply_eq hw)

@[simp] theorem lower_neg_exp_neg_one : lower (-Real.exp (-1)) = -1 := by
  simpa using lower_mulExp (w := -1) le_rfl

theorem strictAntiOn_lower : StrictAntiOn lower (Ico (-Real.exp (-1)) 0) := by
  intro x hx y hy hxy
  by_contra h
  have hle := strictAntiOn_mulExp.antitoneOn (lower_mem hx) (lower_mem hy)
    (le_of_not_gt h)
  rw [mulExp_lower hy, mulExp_lower hx] at hle
  exact (not_le_of_gt hxy) hle

/-- In the interior of their common domain, the two real branches are distinct. -/
theorem lower_lt_principal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lower x < principal x := by
  have hl : lower x ≤ -1 := lower_mem ⟨hx.1.le, hx.2⟩
  have hp : -1 < principal x := by
    simpa using strictMonoOn_principal (show -Real.exp (-1) ∈ Ici (-Real.exp (-1))
      from by simp) hx.1.le hx.1
  exact lt_of_le_of_lt hl hp

/-- The lower branch diverges to `-∞` as its input approaches zero from below. -/
theorem tendsto_lower_nhdsLT_zero :
    Filter.Tendsto lower (nhdsWithin 0 (Iio 0)) Filter.atBot := by
  apply Filter.tendsto_atBot.mpr
  intro b
  let w := min b (-1)
  have hw : w ≤ -1 := min_le_right _ _
  have hbound : -Real.exp (-1) ≤ mulExp w := by
    simpa using strictAntiOn_mulExp.antitoneOn hw
      (show (-1 : ℝ) ∈ Iic (-1) by simp) hw
  filter_upwards [Ioo_mem_nhdsLT (mulExp_neg_of_le_neg_one hw)] with x hx
  have h := strictAntiOn_lower.antitoneOn
    (show mulExp w ∈ Ico (-Real.exp (-1)) 0 from
      ⟨hbound, mulExp_neg_of_le_neg_one hw⟩)
    ⟨hbound.trans hx.1.le, hx.2⟩ hx.1.le
  rw [lower_mulExp hw] at h
  exact h.trans (min_le_left b (-1))

end LambertW.Real
