import SympyProofs.LambertW.EReal
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity

/-! # Continuity of the extended real Lambert W branches -/

namespace LambertW.EReal

open Set

theorem principal_mapsTo : MapsTo principal (Ici ((-Real.exp (-1) : ℝ) : EReal))
    (Ici ((-1 : ℝ) : EReal)) := by
  intro x hx
  simp only [mem_Ici] at *
  induction x with
  | bot => simp at hx
  | top => simp [principal_top]
  | coe x =>
    have hx' : -Real.exp (-1) ≤ x := by exact_mod_cast hx
    change ((-1 : ℝ) : EReal) ≤ (Real.principal x : EReal)
    exact_mod_cast (show -1 ≤ Real.principal x from Real.principal_mem hx')

theorem monotoneOn_principal : MonotoneOn principal (Ici ((-Real.exp (-1) : ℝ) : EReal)) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at *
  induction x with
  | bot => simp at hx
  | top => have : y = ⊤ := top_le_iff.mp hxy; subst y; rfl
  | coe x =>
    induction y with
    | bot => simp at hy
    | top => simp
    | coe y =>
      change (Real.principal x : EReal) ≤ (Real.principal y : EReal)
      apply EReal.coe_le_coe_iff.mpr
      exact Real.strictMonoOn_principal.monotoneOn (by exact_mod_cast hx)
        (by exact_mod_cast hy) (by exact_mod_cast hxy)

theorem principal_surjOn : SurjOn principal (Ici ((-Real.exp (-1) : ℝ) : EReal))
    (Ici ((-1 : ℝ) : EReal)) := by
  intro y hy
  simp only [mem_Ici] at hy
  induction y with
  | bot => exact False.elim ((not_le_of_gt (EReal.bot_lt_coe (-1))) hy)
  | top => exact ⟨⊤, (by simp), principal_top⟩
  | coe w =>
    have hw : -1 ≤ w := by exact_mod_cast hy
    have hb : -Real.exp (-1) ≤ Real.mulExp w := by
      simpa using Real.strictMonoOn_mulExp.monotoneOn (show (-1 : ℝ) ∈ Ici (-1) by simp) hw hw
    refine ⟨(Real.mulExp w : EReal), ?_, ?_⟩
    · change ((-Real.exp (-1) : ℝ) : EReal) ≤ (Real.mulExp w : EReal)
      exact_mod_cast hb
    · simp [Real.principal_mulExp hw]

theorem lower_mapsTo : MapsTo lower (Icc ((-Real.exp (-1) : ℝ) : EReal) 0)
    (Iic ((-1 : ℝ) : EReal)) := by
  intro x hx
  simp only [mem_Iic, mem_Icc] at *
  induction x with
  | bot => simp at hx
  | top => simp at hx
  | coe x =>
    have hx' : -Real.exp (-1) ≤ x ∧ x ≤ 0 := by exact_mod_cast hx
    by_cases h : x = 0
    · subst x; simp
    · rw [lower_coe h]
      exact_mod_cast (show Real.lower x ≤ -1 from Real.lower_mem ⟨hx'.1, lt_of_le_of_ne hx'.2 h⟩)

theorem antitoneOn_lower : AntitoneOn lower (Icc ((-Real.exp (-1) : ℝ) : EReal) 0) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at *
  induction x with
  | bot => simp at hx
  | top => simp at hx
  | coe x =>
    induction y with
    | bot => simp at hy
    | top => simp at hy
    | coe y =>
      have hx' : -Real.exp (-1) ≤ x ∧ x ≤ 0 := by exact_mod_cast hx
      have hy' : -Real.exp (-1) ≤ y ∧ y ≤ 0 := by exact_mod_cast hy
      have hxy' : x ≤ y := by exact_mod_cast hxy
      by_cases h : y = 0
      · subst y; simp
      · have hy0 : y < 0 := lt_of_le_of_ne hy'.2 h
        have hx0 : x ≠ 0 := ne_of_lt (hxy'.trans_lt hy0)
        rw [lower_coe h, lower_coe hx0]
        apply EReal.coe_le_coe_iff.mpr
        exact Real.strictAntiOn_lower.antitoneOn ⟨hx'.1, by linarith⟩
          ⟨hy'.1, by linarith⟩ hxy'

theorem lower_surjOn : SurjOn lower (Icc ((-Real.exp (-1) : ℝ) : EReal) 0)
    (Iic ((-1 : ℝ) : EReal)) := by
  intro y hy
  simp only [mem_Iic] at hy
  induction y with
  | bot =>
    refine ⟨0, ⟨?_, le_rfl⟩, lower_zero⟩
    exact_mod_cast (neg_nonpos.mpr (Real.exp_pos (-1)).le)
  | top => exact False.elim ((not_le_of_gt (EReal.coe_lt_top (-1))) hy)
  | coe w =>
    have hw : w ≤ -1 := by exact_mod_cast hy
    have hb : -Real.exp (-1) ≤ Real.mulExp w := by
      simpa using Real.strictAntiOn_mulExp.antitoneOn hw (show (-1 : ℝ) ∈ Iic (-1) by simp) hw
    have hn := Real.mulExp_neg_of_le_neg_one hw
    refine ⟨(Real.mulExp w : EReal), ?_, ?_⟩
    · simp only [mem_Icc]
      exact_mod_cast (show -Real.exp (-1) ≤ Real.mulExp w ∧ Real.mulExp w ≤ 0 from ⟨hb, hn.le⟩)
    · rw [lower_coe (ne_of_lt hn), Real.lower_mulExp hw]

/-- Continuity on the full extended principal domain, including positive infinity. -/
theorem continuousOn_principal : ContinuousOn principal (Ici ((-Real.exp (-1) : ℝ) : EReal)) := by
  let f : Ici ((-Real.exp (-1) : ℝ) : EReal) → Ici ((-1 : ℝ) : EReal) :=
    fun x => ⟨principal x, principal_mapsTo x.property⟩
  have hm : Monotone f := fun x y h => monotoneOn_principal x.property y.property h
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, h⟩ := principal_surjOn y.property
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp (hm.continuous_of_surjective hs))

/-- Continuity on the full extended lower domain, including the value `-∞` at zero. -/
theorem continuousOn_lower : ContinuousOn lower (Icc ((-Real.exp (-1) : ℝ) : EReal) 0) := by
  let f : Icc ((-Real.exp (-1) : ℝ) : EReal) 0 → Iic ((-1 : ℝ) : EReal) :=
    fun x => ⟨lower x, lower_mapsTo x.property⟩
  have hm : Antitone f := fun x y h => antitoneOn_lower x.property y.property h
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, h⟩ := lower_surjOn y.property
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp (hm.dual_right.continuous_of_surjective hs))

/-- At positive infinity the principal extension tends to its assigned value. -/
theorem tendsto_principal_top :
    Filter.Tendsto principal
      (nhdsWithin ⊤ (Ici ((-Real.exp (-1) : ℝ) : EReal))) (nhds ⊤) := by
  simpa [ContinuousWithinAt] using continuousOn_principal ⊤ (by simp)

/-- At zero the lower extension tends to negative infinity within its valid domain. -/
theorem tendsto_lower_zero :
    Filter.Tendsto lower
      (nhdsWithin 0 (Icc ((-Real.exp (-1) : ℝ) : EReal) 0)) (nhds ⊥) := by
  have hzero : (0 : EReal) ∈ Icc ((-Real.exp (-1) : ℝ) : EReal) 0 := by
    constructor
    · exact_mod_cast (neg_nonpos.mpr (Real.exp_pos (-1)).le)
    · exact le_rfl
  simpa [ContinuousWithinAt] using continuousOn_lower 0 hzero

end LambertW.EReal
