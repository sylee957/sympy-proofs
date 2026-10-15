import SympyProofs.LambertW.Complex.Middle.Endpoint

/-! # Extending a partial lift beyond its endpoint

The endpoint inverse is joined to the existing lift without changing any of
its earlier values. The resulting lift is differentiable through the join.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- Join a partial lift to a compatible analytic endpoint inverse. -/
theorem exists_lift_extension_of_endpoint {F γ g : ℝ → ℂ} {a b : ℝ}
    (hF : ∀ t ∈ Ico a b, DifferentiableAt ℝ F t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hg : ∀ᶠ t in 𝓝 b, DifferentiableAt ℝ g t ∧ mulExp (g t) = γ t)
    (hagree : F =ᶠ[𝓝[<] b] g) :
    ∃ c : ℝ, b < c ∧ ∃ E : ℝ → ℂ,
      EqOn E F (Iio b) ∧
      (∀ t ∈ Ico a c, DifferentiableAt ℝ E t) ∧
      (∀ t ∈ Ico a c, ∀ᶠ s in 𝓝 t, mulExp (E s) = γ s) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hg
  let E : ℝ → ℂ := fun t => if t < b then F t else g t
  have hleft {t : ℝ} (ht : t < b) : E =ᶠ[𝓝 t] F := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    simp [E, hs]
  have hright {t : ℝ} (ht : b ≤ t) : E =ᶠ[𝓝 t] g := by
    rcases ht.eq_or_lt with ht | ht
    · subst t
      filter_upwards [eventually_nhdsWithin_iff.mp hagree] with s hs
      dsimp [E]
      split_ifs with h
      · exact hs h
      · rfl
    · filter_upwards [eventually_gt_nhds ht] with s hs
      simp [E, not_lt_of_ge hs.le]
  refine ⟨b + ε, by linarith, E, (fun t ht => by change t < b at ht; simp [E, ht]), ?_, ?_⟩
  · intro t ht
    by_cases hb : t < b
    · exact (hF t ⟨ht.1, hb⟩).congr_of_eventuallyEq (hleft hb)
    · have hb' := le_of_not_gt hb
      have htb : t ∈ Metric.ball b ε := by
        simp only [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb')]
        linarith [ht.2]
      exact (hball htb).1.congr_of_eventuallyEq (hright hb')
  · intro t ht
    by_cases hb : t < b
    · filter_upwards [hleft hb, hi t ⟨ht.1, hb⟩] with s hs hsi
      rw [hs, hsi]
    · have hb' := le_of_not_gt hb
      have htb : t ∈ Metric.ball b ε := by
        simp only [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb')]
        linarith [ht.2]
      filter_upwards [hright hb', Metric.isOpen_ball.mem_nhds htb] with s hs hsb
      rw [hs]
      exact (hball hsb).2

/-- A partial differentiable lift extends beyond its endpoint if the input
has bounded speed and stays uniformly away from both singular values.
The input path is assumed differentiable on the real line to provide a
continuation past the endpoint. -/
theorem exists_path_lift_extension {F γ F' γ' : ℝ → ℂ} {a b δ η M : ℝ}
    (hab : a < b) (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (F' t) t)
    (hγ : Differentiable ℝ γ)
    (hγ' : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hzero : ∀ t ∈ Ico a b, δ ≤ ‖γ t‖)
    (hcrit : ∀ t ∈ Ico a b, η ≤ ‖γ t + Complex.exp (-1)‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M)
    (hb : γ b ≠ -Complex.exp (-1)) :
    ∃ c : ℝ, b < c ∧ ∃ E : ℝ → ℂ,
      EqOn E F (Iio b) ∧
      (∀ t ∈ Ico a c, DifferentiableAt ℝ E t) ∧
      (∀ t ∈ Ico a c, ∀ᶠ s in 𝓝 t, mulExp (E s) = γ s) := by
  obtain ⟨g, hg, hgi, hcompat⟩ := exists_path_lift_endpoint_continuation
    hab hδ hη hM hF hγ' hi hzero hcrit hspeed
    ((hγ b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hb
  apply exists_lift_extension_of_endpoint (fun t ht => (hF t ht).differentiableAt) hi _ hcompat
  have hn := (hγ b).continuousAt.tendsto.eventually (hg.eventually_analyticAt.and hgi)
  filter_upwards [hn] with t ht
  exact ⟨(ht.1.differentiableAt.hasDerivAt.comp t (hγ t).hasDerivAt).differentiableAt, ht.2⟩

end LambertW.Complex
