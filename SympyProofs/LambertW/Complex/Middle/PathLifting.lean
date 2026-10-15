import SympyProofs.LambertW.Complex.Middle.Gluing
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Whole-interval lifting for bounded-speed paths avoiding the singular values -/

namespace LambertW.Complex

open Set Filter Topology

private def PartialLift (γ : ℝ → ℂ) (a : ℝ) (w : ℂ) (b : ℝ) (F : ℝ → ℂ) : Prop :=
  a < b ∧ F a = w ∧
    (∀ t ∈ Ico a b, DifferentiableAt ℝ F t) ∧
    (∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)

private theorem exists_initial_partialLift {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ)
    {a : ℝ} {w : ℂ} (hw : w ≠ -1) (he : mulExp w = γ a) :
    ∃ b F, PartialLift γ a w b F := by
  obtain ⟨g, r, hr, hga, hgan, hgi⟩ := exists_analytic_inverse_ball hw
  have hn : ∀ᶠ t in 𝓝 a, γ t ∈ Metric.ball (mulExp w) r :=
    (hγ a).continuousAt.tendsto.eventually (by rw [← he]; exact Metric.ball_mem_nhds _ hr)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨a + ε, fun t => g (γ t), by linarith, ?_, ?_, ?_⟩
  · simpa only [← he] using hga
  · intro t ht
    have htb : t ∈ Metric.ball a ε := by
      simp only [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    exact ((hgan _ (hball htb)).differentiableAt.hasDerivAt.comp t (hγ t).hasDerivAt).differentiableAt
  · intro t ht
    have htb : t ∈ Metric.ball a ε := by
      simp only [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    filter_upwards [Metric.isOpen_ball.mem_nhds htb] with s hs
    exact hgi _ (hball hs)

/-- A differentiable input path with bounded speed and uniform separation from
`0` and `-1/e` has a differentiable lift on the entire closed interval, starting
at any prescribed inverse value. Local inverse identities also hold at endpoints. -/
theorem exists_path_lift_on_Icc {γ : ℝ → ℂ} {a B δ η M : ℝ} {w : ℂ}
    (haB : a < B) (hγ : Differentiable ℝ γ)
    (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (hzero : ∀ t ∈ Icc a B, δ ≤ ‖γ t‖)
    (hcrit : ∀ t ∈ Icc a B, η ≤ ‖γ t + Complex.exp (-1)‖)
    (hspeed : ∀ t ∈ Icc a B, ‖deriv γ t‖ ≤ M)
    (hstart : mulExp w = γ a) :
    ∃ F : ℝ → ℂ, F a = w ∧
      (∀ t ∈ Icc a B, DifferentiableAt ℝ F t) ∧
      (∀ t ∈ Icc a B, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s) := by
  classical
  have havoid : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1) := by
    intro t ht he
    have hh := hcrit t ht
    rw [he] at hh
    simp at hh
    linarith
  have hw : w ≠ -1 := by
    intro hw
    rw [hw, mulExp_neg_one] at hstart
    exact havoid a ⟨le_rfl, haB.le⟩ hstart.symm
  let S : Set ℝ := {b | b ≤ B ∧ ∃ F, PartialLift γ a w b F}
  obtain ⟨d, F₀, hd, hF₀⟩ := exists_initial_partialLift hγ hw hstart
  have hs₀ : min d B ∈ S := by
    refine ⟨min_le_right _ _, F₀, lt_min hd haB, hF₀.1, ?_, ?_⟩
    · intro t ht; exact hF₀.2.1 t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    · intro t ht; exact hF₀.2.2 t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hSne : S.Nonempty := ⟨_, hs₀⟩
  have hSbdd : BddAbove S := ⟨B, fun b hb => hb.1⟩
  let c := sSup S
  have hcB : c ≤ B := csSup_le hSne (fun b hb => hb.1)
  have hac : a < c := (lt_min hd haB).trans_le (le_csSup hSbdd hs₀)
  let f : S → ℝ → ℂ := fun i => i.property.2.choose
  have hf (i : S) : PartialLift γ a w i.val (f i) := i.property.2.choose_spec
  obtain ⟨E, hEa, hEq, hElocal, hEd, hEi⟩ := exists_glued_partial_lifts
    (ι := S) ⟨min d B, hs₀⟩ (F := f) (b := fun i => i.val)
    (fun i => (hf i).1) (fun i => (hf i).2.2.1) (fun i => (hf i).2.2.2)
    (fun i => (hf i).2.1)
    (fun i t ht => havoid t ⟨ht.1, ht.2.le.trans i.property.1⟩)
  have hcover {t : ℝ} (ht : t ∈ Ico a c) : ∃ i : S, t ∈ Ico a i.val := by
    obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hSne ht.2
    exact ⟨⟨b, hb⟩, ht.1, htb⟩
  have hEder : ∀ t ∈ Ico a c, DifferentiableAt ℝ E t := by
    intro t ht; obtain ⟨i, hi⟩ := hcover ht; exact hEd i t hi
  have hEinv : ∀ t ∈ Ico a c, ∀ᶠ s in 𝓝 t, mulExp (E s) = γ s := by
    intro t ht; obtain ⟨i, hi⟩ := hcover ht; exact hEi i t hi
  have hsub : Ico a c ⊆ Icc a B := fun t ht => ⟨ht.1, ht.2.le.trans hcB⟩
  obtain ⟨e, hce, G, hGE, hGd, hGi⟩ := exists_path_lift_extension
    hac hδ hη hM (fun t ht => (hEder t ht).hasDerivAt) hγ
    (fun t _ => (hγ t).hasDerivAt) hEinv
    (fun t ht => hzero t (hsub ht)) (fun t ht => hcrit t (hsub ht))
    (fun t ht => hspeed t (hsub ht)) (havoid c ⟨hac.le, hcB⟩)
  have hGa : G a = w := (hGE hac).trans hEa
  have hBc : B ≤ c := by
    by_contra hh
    have hcB' : c < B := lt_of_not_ge hh
    have hs : min e B ∈ S := by
      refine ⟨min_le_right _ _, G, hac.trans (lt_min hce hcB'), hGa, ?_, ?_⟩
      · intro t ht; exact hGd t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      · intro t ht; exact hGi t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have hh := le_csSup hSbdd hs
    exact (not_le_of_gt (lt_min hce hcB')) hh
  have hBe : B < e := hBc.trans_lt hce
  exact ⟨G, hGa, (fun t ht => hGd t ⟨ht.1, ht.2.trans_lt hBe⟩),
    (fun t ht => hGi t ⟨ht.1, ht.2.trans_lt hBe⟩)⟩

/-- For a continuously differentiable path, compactness supplies all the speed
and separation bounds needed by whole-interval existence. -/
theorem exists_smooth_path_lift_on_Icc {γ : ℝ → ℂ} {a B : ℝ} {w : ℂ}
    (haB : a < B) (hγ : ContDiff ℝ 1 γ)
    (hzero : ∀ t ∈ Icc a B, γ t ≠ 0)
    (hcrit : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1))
    (hstart : mulExp w = γ a) :
    ∃ F : ℝ → ℂ, F a = w ∧
      (∀ t ∈ Icc a B, DifferentiableAt ℝ F t) ∧
      (∀ t ∈ Icc a B, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s) := by
  obtain ⟨δ, hδ, hδbound⟩ := isCompact_Icc.exists_forall_le'
    hγ.continuous.norm.continuousOn (fun t ht => norm_pos_iff.mpr (hzero t ht))
  obtain ⟨η, hη, hηbound⟩ := isCompact_Icc.exists_forall_le'
    (hγ.continuous.add continuous_const).norm.continuousOn
    (fun t ht => norm_pos_iff.mpr (show γ t + Complex.exp (-1) ≠ 0 from
      fun he => hcrit t ht (eq_neg_of_add_eq_zero_left he)))
  obtain ⟨M, hMbound⟩ := isCompact_Icc.bddAbove_image hγ.continuous_deriv_one.norm.continuousOn
  apply exists_path_lift_on_Icc haB (hγ.differentiable (by norm_num)) hδ hη
    (le_max_left 0 M) hδbound hηbound _ hstart
  intro t ht
  exact (hMbound ⟨t, ht, rfl⟩).trans (le_max_right 0 M)

/-- Capstone: every `C¹` path avoiding `0` and `-1/e` on a compact interval has
exactly one continuous lift from a prescribed inverse value. Uniqueness is of
the restricted function on the interval, not of arbitrary off-interval values. -/
theorem existsUnique_continuous_path_lift {γ : ℝ → ℂ} {a B : ℝ} {w : ℂ}
    (haB : a < B) (hγ : ContDiff ℝ 1 γ)
    (hzero : ∀ t ∈ Icc a B, γ t ≠ 0)
    (hcrit : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1))
    (hstart : mulExp w = γ a) :
    ∃! F : Icc a B → ℂ, Continuous F ∧
      F ⟨a, le_rfl, haB.le⟩ = w ∧ ∀ t, mulExp (F t) = γ t := by
  obtain ⟨F, hFa, hFd, hFi⟩ := exists_smooth_path_lift_on_Icc haB hγ hzero hcrit hstart
  have hFc : Continuous (fun t : Icc a B => F t) :=
    continuousOn_iff_continuous_domRestrict.mp
      (fun t ht => (hFd t ht).continuousAt.continuousWithinAt)
  have hFright : ∀ t : Icc a B, mulExp (F t) = γ t :=
    fun t => (hFi t t.property).self_of_nhds
  refine ⟨fun t => F t, ⟨hFc, hFa, hFright⟩, ?_⟩
  intro G hG
  let : PreconnectedSpace (Icc a B) := Subtype.preconnectedSpace isPreconnected_Icc
  apply eq_of_continuous_mulExp_lifts hG.1 hFc
    (fun t => (hG.2.2 t).trans (hFright t).symm)
    (fun t => by rw [hG.2.2 t]; exact hcrit t t.property)
    (t₀ := ⟨a, le_rfl, haB.le⟩)
  exact hG.2.1.trans hFa.symm

/-- Capstone for the middle branch: its real value at the start determines a
unique continuous lift along the whole nonsingular `C¹` complex path. -/
theorem existsUnique_middle_path_lift {γ : ℝ → ℂ} {a B x : ℝ}
    (haB : a < B) (hγ : ContDiff ℝ 1 γ)
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) (hstart : γ a = (x : ℂ))
    (hzero : ∀ t ∈ Icc a B, γ t ≠ 0)
    (hcrit : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1)) :
    ∃! F : Icc a B → ℂ, Continuous F ∧
      F ⟨a, le_rfl, haB.le⟩ = (Real.lower x : ℂ) ∧
      ∀ t, mulExp (F t) = γ t := by
  apply existsUnique_continuous_path_lift haB hγ hzero hcrit
  rw [mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩, hstart]

/-- The whole lift is analytic continuation in the input variable: at every
time, including endpoints, it locally factors through an analytic inverse.
The path itself need only be `C¹`, not analytic. -/
theorem exists_analytic_continuation_along_path {γ : ℝ → ℂ} {a B : ℝ} {w : ℂ}
    (haB : a < B) (hγ : ContDiff ℝ 1 γ)
    (hzero : ∀ t ∈ Icc a B, γ t ≠ 0)
    (hcrit : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1))
    (hstart : mulExp w = γ a) :
    ∃ F : ℝ → ℂ, F a = w ∧
      (∀ t ∈ Icc a B, DifferentiableAt ℝ F t) ∧
      (∀ t ∈ Icc a B, mulExp (F t) = γ t) ∧
      ∀ t ∈ Icc a B, ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (γ t) ∧ g (γ t) = F t ∧
        (∀ᶠ z in 𝓝 (γ t), mulExp (g z) = z) ∧
        (∀ᶠ s in 𝓝 t, F s = g (γ s)) := by
  obtain ⟨F, hFa, hFd, hFi⟩ := exists_smooth_path_lift_on_Icc haB hγ hzero hcrit hstart
  have hval : ∀ t ∈ Icc a B, mulExp (F t) = γ t := fun t ht => (hFi t ht).self_of_nhds
  refine ⟨F, hFa, hFd, hval, ?_⟩
  intro t ht
  have hn : F t ≠ -1 := by
    intro he
    have hh := hval t ht
    rw [he, mulExp_neg_one] at hh
    exact hcrit t ht hh.symm
  obtain ⟨g, hg, hleft, hright⟩ := exists_analytic_localInverse hn
  have hcenter := hleft.self_of_nhds
  rw [hval t ht] at hg hright hcenter
  refine ⟨g, hg, hcenter, hright, ?_⟩
  filter_upwards [(hFd t ht).continuousAt.tendsto.eventually hleft, hFi t ht] with s hs hi
  rw [hi] at hs
  exact hs.symm

/-- Analytic continuation of the real lower germ along any nonsingular `C¹`
path on a compact interval. This remains path-dependent until a monodromy
or path-independence theorem is established on a chosen domain. -/
theorem exists_middle_analytic_continuation {γ : ℝ → ℂ} {a B x : ℝ}
    (haB : a < B) (hγ : ContDiff ℝ 1 γ)
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) (hstart : γ a = (x : ℂ))
    (hzero : ∀ t ∈ Icc a B, γ t ≠ 0)
    (hcrit : ∀ t ∈ Icc a B, γ t ≠ -Complex.exp (-1)) :
    ∃ F : ℝ → ℂ, F a = (Real.lower x : ℂ) ∧
      (∀ t ∈ Icc a B, DifferentiableAt ℝ F t) ∧
      (∀ t ∈ Icc a B, mulExp (F t) = γ t) ∧
      ∀ t ∈ Icc a B, ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (γ t) ∧ g (γ t) = F t ∧
        (∀ᶠ z in 𝓝 (γ t), mulExp (g z) = z) ∧
        (∀ᶠ s in 𝓝 t, F s = g (γ s)) := by
  apply exists_analytic_continuation_along_path haB hγ hzero hcrit
  rw [mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩, hstart]

end LambertW.Complex
