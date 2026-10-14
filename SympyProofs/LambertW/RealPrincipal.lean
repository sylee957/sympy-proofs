import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The real principal branch of Lambert W

The map `w ↦ w * exp w` is strictly increasing on `[-1, ∞)` and has image
`[-exp (-1), ∞)`. Its inverse on these intervals is `principal`.
Outside this input domain, `principal` has an unspecified value.
-/

namespace LambertW.Real

open Set

/-- The function inverted by Lambert W. -/
noncomputable def mulExp (w : ℝ) : ℝ := w * Real.exp w

theorem continuous_mulExp : Continuous mulExp :=
  continuous_id.mul Real.continuous_exp

theorem hasDerivAt_mulExp (w : ℝ) :
    HasDerivAt mulExp (Real.exp w * (1 + w)) w := by
  convert (hasDerivAt_id w).mul (Real.hasDerivAt_exp w) using 1
  · rfl
  · change Real.exp w * (1 + w) = 1 * Real.exp w + w * Real.exp w
    ring

theorem strictMonoOn_mulExp : StrictMonoOn mulExp (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (-1)) continuous_mulExp.continuousOn
  intro w hw
  rw [(hasDerivAt_mulExp w).deriv]
  have hw' : -1 < w := by simpa using hw
  exact mul_pos (Real.exp_pos w) (by linarith)

@[simp] theorem mulExp_neg_one : mulExp (-1) = -Real.exp (-1) := by
  simp [mulExp]

@[simp] theorem mulExp_zero : mulExp 0 = 0 := by
  simp [mulExp]

/-- Existence uses the intermediate value theorem on `[-1, max x 0]`. -/
theorem exists_mulExp_eq {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    ∃ w ∈ Ici (-1 : ℝ), mulExp w = x := by
  have hb : 0 ≤ max x 0 := le_max_right _ _
  have he : 1 ≤ Real.exp (max x 0) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hb
  have hupper : x ≤ mulExp (max x 0) := by
    calc
      x ≤ max x 0 := le_max_left _ _
      _ ≤ mulExp (max x 0) := by
        simpa [mulExp] using mul_le_mul_of_nonneg_left he hb
  obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc (by linarith : (-1 : ℝ) ≤ max x 0)
    continuous_mulExp.continuousOn ⟨by simpa using hx, hupper⟩
  exact ⟨w, hw.1, hwe⟩

theorem existsUnique_mulExp_eq {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    ∃! w : ℝ, w ∈ Ici (-1 : ℝ) ∧ mulExp w = x := by
  obtain ⟨w, hw, hwe⟩ := exists_mulExp_eq hx
  refine ⟨w, ⟨hw, hwe⟩, ?_⟩
  intro v hv
  exact strictMonoOn_mulExp.injOn hv.1 hw (hv.2.trans hwe.symm)

/-- The real principal branch, specified for `-exp (-1) ≤ x`. -/
noncomputable def principal : ℝ → ℝ :=
  Function.invFunOn mulExp (Ici (-1))

theorem principal_mem {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    principal x ∈ Ici (-1 : ℝ) :=
  Function.invFunOn_mem (exists_mulExp_eq hx)

theorem mulExp_principal {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    mulExp (principal x) = x :=
  Function.invFunOn_eq (exists_mulExp_eq hx)

theorem principal_mul_exp {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    principal x * Real.exp (principal x) = x :=
  mulExp_principal hx

theorem principal_mulExp {w : ℝ} (hw : -1 ≤ w) :
    principal (mulExp w) = w := by
  exact strictMonoOn_mulExp.injOn (Function.invFunOn_apply_mem hw) hw
    (Function.invFunOn_apply_eq hw)

@[simp] theorem principal_zero : principal 0 = 0 := by
  simpa using principal_mulExp (w := 0) (by norm_num)

@[simp] theorem principal_neg_exp_neg_one :
    principal (-Real.exp (-1)) = -1 := by
  simpa using principal_mulExp (w := -1) le_rfl

theorem strictMonoOn_principal :
    StrictMonoOn principal (Ici (-Real.exp (-1))) := by
  intro x hx y hy hxy
  by_contra h
  have hle := strictMonoOn_mulExp.monotoneOn (principal_mem hy) (principal_mem hx)
    (le_of_not_gt h)
  rw [mulExp_principal hy, mulExp_principal hx] at hle
  exact (not_le_of_gt hxy) hle

/-- The principal branch diverges to `+∞` as its input tends to `+∞`. -/
theorem tendsto_principal_atTop :
    Filter.Tendsto principal Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  let w := max b (-1)
  have hw : -1 ≤ w := le_max_right _ _
  have hbound : -Real.exp (-1) ≤ mulExp w := by
    simpa using strictMonoOn_mulExp.monotoneOn (show (-1 : ℝ) ∈ Set.Ici (-1) by simp)
      hw hw
  refine ⟨mulExp w, fun x hx => ?_⟩
  have h := strictMonoOn_principal.monotoneOn hbound (hbound.trans hx) hx
  rw [principal_mulExp hw] at h
  exact (le_max_left b (-1)).trans h

end LambertW.Real
