import SympyProofs.LambertW.Complex.Middle.Extension

/-! # Compatibility and gluing of partial path lifts -/

namespace LambertW.Complex

open Set Filter Topology

/-- Continuous lifts on two initial time intervals agree on their overlap. -/
theorem eqOn_partial_lifts {F G γ : ℝ → ℂ} {a b c : ℝ}
    (hab : a < b) (hac : a < c)
    (hF : ContinuousOn F (Ico a b)) (hG : ContinuousOn G (Ico a c))
    (hFi : ∀ t ∈ Ico a b, mulExp (F t) = γ t)
    (hGi : ∀ t ∈ Ico a c, mulExp (G t) = γ t)
    (havoid : ∀ t ∈ Ico a (min b c), γ t ≠ -Complex.exp (-1))
    (hstart : F a = G a) : EqOn F G (Ico a (min b c)) := by
  let S := Ico a (min b c)
  let : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Ico
  have hsubF : S ⊆ Ico a b := fun t ht => ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hsubG : S ⊆ Ico a c := fun t ht => ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have he : (fun t : S => F t) = (fun t : S => G t) := by
    apply eq_of_continuous_mulExp_lifts (T := S) (F := fun t : S => F t) (G := fun t : S => G t)
      (continuousOn_iff_continuous_domRestrict.mp (hF.mono hsubF)) (continuousOn_iff_continuous_domRestrict.mp (hG.mono hsubG))
      (fun t => (hFi t (hsubF t.property)).trans (hGi t (hsubG t.property)).symm)
      (fun t => by rw [hFi t (hsubF t.property)]; exact havoid t t.property)
      (t₀ := ⟨a, le_rfl, lt_min hab hac⟩)
    exact hstart
  intro t ht
  exact congrFun he ⟨t, ht⟩

/-- An arbitrary family of partial lifts with the same initial value can be
joined. The joined function agrees locally with each member, including at
the initial endpoint, so differentiability and local inverse identities survive. -/
theorem exists_glued_partial_lifts {ι : Type*} (i₀ : ι)
    {F : ι → ℝ → ℂ} {γ : ℝ → ℂ} {a : ℝ} {b : ι → ℝ} {w : ℂ}
    (hab : ∀ i, a < b i)
    (hF : ∀ i t, t ∈ Ico a (b i) → DifferentiableAt ℝ (F i) t)
    (hi : ∀ i t, t ∈ Ico a (b i) → ∀ᶠ s in 𝓝 t, mulExp (F i s) = γ s)
    (hstart : ∀ i, F i a = w)
    (havoid : ∀ i t, t ∈ Ico a (b i) → γ t ≠ -Complex.exp (-1)) :
    ∃ E : ℝ → ℂ, E a = w ∧
      (∀ i, EqOn E (F i) (Ico a (b i))) ∧
      (∀ i t, t ∈ Ico a (b i) → E =ᶠ[𝓝 t] F i) ∧
      (∀ i t, t ∈ Ico a (b i) → DifferentiableAt ℝ E t) ∧
      (∀ i t, t ∈ Ico a (b i) → ∀ᶠ s in 𝓝 t, mulExp (E s) = γ s) := by
  classical
  have hpair (i j : ι) : EqOn (F i) (F j) (Ico a (min (b i) (b j))) := by
    apply eqOn_partial_lifts (hab i) (hab j)
      (fun t ht => (hF i t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hF j t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hi i t ht).self_of_nhds) (fun t ht => (hi j t ht).self_of_nhds)
      (fun t ht => havoid i t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
    rw [hstart i, hstart j]
  let E : ℝ → ℂ := fun t =>
    if h : ∃ i, t ∈ Ico a (b i) then F h.choose t else F i₀ t
  have heq (i : ι) {t : ℝ} (ht : t ∈ Ico a (b i)) : E t = F i t := by
    have hex : ∃ j, t ∈ Ico a (b j) := ⟨i, ht⟩
    simp only [E, dite_eq_left hex]
    exact hpair hex.choose i ⟨ht.1, lt_min hex.choose_spec.2 ht.2⟩
  have hlocal (i : ι) {t : ℝ} (ht : t ∈ Ico a (b i)) : E =ᶠ[𝓝 t] F i := by
    rcases ht.1.eq_or_lt with he | he
    · subst t
      have hne : F i₀ a ≠ -1 := by
        intro hn
        have hh := (hi i₀ a ⟨le_rfl, hab i₀⟩).self_of_nhds
        rw [hn, mulExp_neg_one] at hh
        exact havoid i₀ a ⟨le_rfl, hab i₀⟩ hh.symm
      have hsame : F i₀ =ᶠ[𝓝 a] F i := by
        apply eventuallyEq_mulExp_lifts (hF i₀ a ⟨le_rfl, hab i₀⟩).continuousAt
          (hF i a ⟨le_rfl, hab i⟩).continuousAt
          ((hstart i₀).trans (hstart i).symm) hne
        filter_upwards [hi i₀ a ⟨le_rfl, hab i₀⟩, hi i a ⟨le_rfl, hab i⟩] with s hs hs'
        exact hs.trans hs'.symm
      filter_upwards [hsame, eventually_lt_nhds (hab i)] with s hs hsb
      by_cases has : a ≤ s
      · exact heq i ⟨has, hsb⟩
      · have hnone : ¬ ∃ j, s ∈ Ico a (b j) := by rintro ⟨j, hj⟩; exact has hj.1
        simpa only [E, dite_eq_right hnone] using hs
    · filter_upwards [Ioo_mem_nhds he ht.2] with s hs
      exact heq i ⟨hs.1.le, hs.2⟩
  refine ⟨E, (heq i₀ ⟨le_rfl, hab i₀⟩).trans (hstart i₀),
    (fun i t ht => heq i ht), (fun i t ht => hlocal i ht), ?_, ?_⟩
  · intro i t ht
    exact (hF i t ht).congr_of_eventuallyEq (hlocal i ht)
  · intro i t ht
    filter_upwards [hlocal i ht, hi i t ht] with s hs hsi
    rw [hs, hsi]

end LambertW.Complex
