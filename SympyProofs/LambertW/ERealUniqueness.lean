import SympyProofs.LambertW.ERealContinuity

/-!
# Uniqueness of the continuous extended real Lambert W branches

Agreement is required only on the original finite real domains. Continuity
forces the new endpoint values. Uniqueness is restricted to the valid extended
domains; no condition is imposed on the totalization values outside them.
-/

namespace LambertW.EReal

open Set Filter Topology

/-- Agreement with the real principal branch and continuity force the value at infinity. -/
theorem principal_extension_top {f : EReal → EReal}
    (hc : ContinuousOn f (Ici ((-Real.exp (-1) : ℝ) : EReal)))
    (ha : ∀ x : ℝ, -Real.exp (-1) ≤ x → f (x : EReal) = (Real.principal x : EReal)) :
    f ⊤ = ⊤ := by
  have hin : Tendsto (fun x : ℝ => (x : EReal)) atTop
      (nhdsWithin ⊤ (Ici ((-Real.exp (-1) : ℝ) : EReal))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨EReal.tendsto_coe_atTop, ?_⟩
    filter_upwards [eventually_ge_atTop (-Real.exp (-1))] with x hx
    change ((-Real.exp (-1) : ℝ) : EReal) ≤ (x : EReal)
    exact_mod_cast hx
  have hf := (hc ⊤ (by simp)).tendsto.comp hin
  have he : (fun x : ℝ => f (x : EReal)) =ᶠ[atTop]
      (fun x : ℝ => (Real.principal x : EReal)) := by
    filter_upwards [eventually_ge_atTop (-Real.exp (-1))] with x hx
    exact ha x hx
  exact tendsto_nhds_unique (hf.congr' he)
    (EReal.tendsto_coe_atTop.comp Real.tendsto_principal_atTop)

/-- Agreement with the real lower branch and continuity force negative infinity at zero. -/
theorem lower_extension_zero {f : EReal → EReal}
    (hc : ContinuousOn f (Icc ((-Real.exp (-1) : ℝ) : EReal) 0))
    (ha : ∀ x : ℝ, x ∈ Ico (-Real.exp (-1)) 0 → f (x : EReal) = (Real.lower x : EReal)) :
    f 0 = ⊥ := by
  have hb : -Real.exp (-1) < 0 := neg_neg_of_pos (Real.exp_pos (-1))
  have hz : (0 : EReal) ∈ Icc ((-Real.exp (-1) : ℝ) : EReal) 0 := by
    constructor
    · exact_mod_cast hb.le
    · exact le_rfl
  have hin : Tendsto (fun x : ℝ => (x : EReal)) (nhdsWithin 0 (Iio 0))
      (nhdsWithin 0 (Icc ((-Real.exp (-1) : ℝ) : EReal) 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using continuous_coe_real_ereal.continuousAt.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Iio 0) ≤ nhds 0 from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsLT hb] with x hx
      simp only [mem_Icc]
      exact_mod_cast (show -Real.exp (-1) ≤ x ∧ x ≤ 0 from ⟨hx.1.le, hx.2.le⟩)
  have hf := (hc 0 hz).tendsto.comp hin
  have he : (fun x : ℝ => f (x : EReal)) =ᶠ[nhdsWithin 0 (Iio 0)]
      (fun x : ℝ => (Real.lower x : EReal)) := by
    filter_upwards [Ioo_mem_nhdsLT hb] with x hx
    exact ha x ⟨hx.1.le, hx.2⟩
  exact tendsto_nhds_unique (hf.congr' he)
    (EReal.tendsto_coe_atBot.comp Real.tendsto_lower_nhdsLT_zero)

/-- The principal branch has a unique continuous extension on its extended domain. -/
theorem principal_extension_unique {f : EReal → EReal}
    (hc : ContinuousOn f (Ici ((-Real.exp (-1) : ℝ) : EReal)))
    (ha : ∀ x : ℝ, -Real.exp (-1) ≤ x → f (x : EReal) = (Real.principal x : EReal)) :
    EqOn f principal (Ici ((-Real.exp (-1) : ℝ) : EReal)) := by
  intro x hx
  induction x with
  | bot => simp at hx
  | top => simpa using principal_extension_top hc ha
  | coe x =>
    rw [principal_coe]
    apply ha
    exact_mod_cast (show ((-Real.exp (-1) : ℝ) : EReal) ≤ (x : EReal) from hx)

/-- The lower branch has a unique continuous extension on its extended domain. -/
theorem lower_extension_unique {f : EReal → EReal}
    (hc : ContinuousOn f (Icc ((-Real.exp (-1) : ℝ) : EReal) 0))
    (ha : ∀ x : ℝ, x ∈ Ico (-Real.exp (-1)) 0 → f (x : EReal) = (Real.lower x : EReal)) :
    EqOn f lower (Icc ((-Real.exp (-1) : ℝ) : EReal) 0) := by
  intro x hx
  induction x with
  | bot => simp at hx
  | top => simp at hx
  | coe x =>
    by_cases h : x = 0
    · subst x
      simpa using lower_extension_zero hc ha
    · rw [lower_coe h]
      apply ha
      have hx' : -Real.exp (-1) ≤ x ∧ x ≤ 0 := by
        simp only [mem_Icc] at hx
        exact_mod_cast hx
      exact ⟨hx'.1, lt_of_le_of_ne hx'.2 h⟩

end LambertW.EReal
