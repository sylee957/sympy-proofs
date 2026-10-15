import SympyProofs.LambertW.Complex.Middle.PathUniqueness

/-!
# Local existence of lifts of complex paths

Every continuous input path lifts on a neighborhood of a parameter at which
a noncritical inverse value is prescribed. The lift is unique as a germ.
This is local path lifting; it does not assert existence on the full interval.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- A noncritical inverse is analytic and a right inverse on an actual disk. -/
theorem exists_analytic_inverse_ball {w : ℂ} (hw : w ≠ -1) :
    ∃ g : ℂ → ℂ, ∃ r : ℝ, 0 < r ∧ g (mulExp w) = w ∧
      AnalyticOnNhd ℂ g (Metric.ball (mulExp w) r) ∧
      ∀ z ∈ Metric.ball (mulExp w) r, mulExp (g z) = z := by
  obtain ⟨g, hg, hcenter, hd, hi, hcompat⟩ := exists_analytic_inverse_continuation hw
  obtain ⟨a, ha, hga⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨b, hb, hgb⟩ := Metric.mem_nhds_iff.mp hi
  refine ⟨g, min a b, lt_min ha hb, hcenter, ?_, ?_⟩
  · intro z hz
    exact hga z (lt_of_lt_of_le hz (min_le_left a b))
  · intro z hz
    exact hgb (lt_of_lt_of_le hz (min_le_right a b))

/-- Local lifting for any continuous family of complex inputs. The lift exists
on an open neighborhood and is uniquely determined there as a germ by its value. -/
theorem exists_local_mulExp_lift {T : Type*} [TopologicalSpace T]
    {γ : T → ℂ} (hγ : Continuous γ) {t₀ : T} {w : ℂ}
    (hw : w ≠ -1) (hstart : mulExp w = γ t₀) :
    ∃ U : Set T, IsOpen U ∧ t₀ ∈ U ∧ ∃ F : T → ℂ,
      ContinuousOn F U ∧ F t₀ = w ∧ (∀ t ∈ U, mulExp (F t) = γ t) ∧
      ∀ G : T → ℂ, ContinuousAt G t₀ → G t₀ = w →
        (∀ᶠ t in 𝓝 t₀, mulExp (G t) = γ t) → F =ᶠ[𝓝 t₀] G := by
  obtain ⟨g, r, hr, hcenter, hga, hgi⟩ := exists_analytic_inverse_ball hw
  let U := γ ⁻¹' Metric.ball (mulExp w) r
  have hU : IsOpen U := Metric.isOpen_ball.preimage hγ
  have ht : t₀ ∈ U := by simpa [U, hstart] using hr
  let F : T → ℂ := fun t => g (γ t)
  have hFc : ∀ t ∈ U, ContinuousAt F t := by
    intro t ht
    exact (hga _ ht).continuousAt.comp hγ.continuousAt
  have hF0 : F t₀ = w := by simpa only [F, ← hstart] using hcenter
  have hFi : ∀ t ∈ U, mulExp (F t) = γ t := fun t ht => hgi _ ht
  refine ⟨U, hU, ht, F, fun t ht => (hFc t ht).continuousWithinAt, hF0, hFi, ?_⟩
  intro G hG hG0 hGi
  apply eventuallyEq_mulExp_lifts (hFc t₀ ht) hG (hF0.trans hG0.symm)
    (by simpa only [hF0] using hw)
  filter_upwards [hU.mem_nhds ht, hGi] with t ht hGt
  exact (hFi t ht).trans hGt.symm

/-- Starting at any real lower-branch value, an arbitrary continuous complex
path has a locally unique middle lift, even if it immediately leaves the real axis. -/
theorem exists_local_middle_path_lift {γ : unitInterval → ℂ} (hγ : Continuous γ)
    {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) (hstart : γ 0 = (x : ℂ)) :
    ∃ U : Set unitInterval, IsOpen U ∧ 0 ∈ U ∧ ∃ F : unitInterval → ℂ,
      ContinuousOn F U ∧ F 0 = (Real.lower x : ℂ) ∧
      (∀ t ∈ U, mulExp (F t) = γ t) ∧
      ∀ G : unitInterval → ℂ, ContinuousAt G 0 → G 0 = (Real.lower x : ℂ) →
        (∀ᶠ t in 𝓝 0, mulExp (G t) = γ t) → F =ᶠ[𝓝 0] G := by
  apply exists_local_mulExp_lift hγ
  · intro he
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
    have hl := Real.lower_lt_neg_one hx
    linarith
  · rw [mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩, hstart]

end LambertW.Complex
