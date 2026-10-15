import SympyProofs.LambertW.Complex.Middle.Continuation
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.UnitInterval

/-!
# Uniqueness of continuous lifts of Lambert W paths

Continuous lifts of the same input path coincide if they start at the same
value and the input avoids the critical value. The result holds on any
preconnected parameter space. It proves uniqueness of an existing lift, not
existence of lifts or independence from the input path.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- Continuous lifts are locally identical wherever they meet at a noncritical value. -/
theorem eventuallyEq_mulExp_lifts {T : Type*} [TopologicalSpace T]
    {F G : T → ℂ} {t : T} (hF : ContinuousAt F t) (hG : ContinuousAt G t)
    (he : F t = G t) (hn : F t ≠ -1)
    (hi : ∀ᶠ s in 𝓝 t, mulExp (F s) = mulExp (G s)) :
    F =ᶠ[𝓝 t] G := by
  obtain ⟨g, hg, hleft, hright⟩ := exists_analytic_localInverse hn
  have hGt : Tendsto G (𝓝 t) (𝓝 (F t)) := by simpa only [he] using hG.tendsto
  filter_upwards [hF.tendsto.eventually hleft, hGt.eventually hleft, hi] with s hf hg hs
  rw [← hf, ← hg, hs]

/-- A lift of the forward map is uniquely determined by one value on a
preconnected parameter space, provided the common image avoids `-1/e`. -/
theorem eq_of_continuous_mulExp_lifts {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] {F G : T → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hi : ∀ t, mulExp (F t) = mulExp (G t))
    (hn : ∀ t, mulExp (F t) ≠ -Complex.exp (-1))
    {t₀ : T} (hstart : F t₀ = G t₀) : F = G := by
  let S : Set T := {t | F t = G t}
  have hc : IsClosed S := isClosed_eq hF hG
  have ho : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hw : F t ≠ -1 := by
      intro hw
      apply hn t
      rw [hw, mulExp_neg_one]
    exact eventuallyEq_mulExp_lifts hF.continuousAt hG.continuousAt ht hw
      (Filter.Eventually.of_forall hi)
  have hall : S = univ := (show IsClopen S from ⟨hc, ho⟩).eq_univ ⟨t₀, hstart⟩
  funext t
  have ht : t ∈ S := by rw [hall]; trivial
  exact ht

/-- In particular, continuous lifts of a path on `[0,1]` with the same initial
value agree at every time, and hence at the endpoint. -/
theorem eq_of_middle_path_lifts {γ F G : unitInterval → ℂ}
    (hF : Continuous F) (hG : Continuous G)
    (hFi : ∀ t, mulExp (F t) = γ t) (hGi : ∀ t, mulExp (G t) = γ t)
    (havoid : ∀ t, γ t ≠ -Complex.exp (-1)) (hstart : F 0 = G 0) : F = G := by
  apply eq_of_continuous_mulExp_lifts hF hG
    (fun t => (hFi t).trans (hGi t).symm) _ hstart
  intro t
  rw [hFi t]
  exact havoid t

/-- Every continuous real path in `(-1/e,0)` has a unique continuous complex
lift starting on the middle branch. Along such paths the lift is `Real.lower`. -/
theorem existsUnique_real_lower_path_lift {γ : unitInterval → ℝ}
    (hγ : Continuous γ) (hdom : ∀ t, γ t ∈ Ioo (-Real.exp (-1)) 0) :
    ∃! F : unitInterval → ℂ, Continuous F ∧
      (∀ t, mulExp (F t) = (γ t : ℂ)) ∧ F 0 = (Real.lower (γ 0) : ℂ) := by
  let F : unitInterval → ℂ := fun t => (Real.lower (γ t) : ℂ)
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_lower (hdom t)).comp hγ.continuousAt)
  have hi : ∀ t, mulExp (F t) = (γ t : ℂ) := by
    intro t
    exact (mulExp_ofReal _).trans (congrArg Complex.ofReal
      (Real.mulExp_lower ⟨(hdom t).1.le, (hdom t).2⟩))
  refine ⟨F, ⟨hF, hi, rfl⟩, ?_⟩
  intro G hG
  apply eq_of_middle_path_lifts hG.1 hF hG.2.1 hi _ hG.2.2
  intro t he
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.exp_re,
    Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im,
    neg_zero, Real.cos_zero, mul_one] at hre
  have ht := (hdom t).1
  linarith

end LambertW.Complex
