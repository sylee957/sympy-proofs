import SympyProofs.LambertW.Complex.Middle.PathLifting
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Convex

/-! # Continuous families of inverse branches -/

namespace LambertW.Complex

open Set Filter Topology

private abbrev Regular := {w : ℂ // w ≠ -1}

private noncomputable def regularMulExp (w : Regular) : ℂ := mulExp w

private theorem regularMulExp_localHomeomorph : IsLocalHomeomorph regularMulExp := by
  have hm : IsLocalHomeomorphOn mulExp {w : ℂ | w ≠ -1} := by
    intro w hw
    let h := (analyticAt_mulExp w).hasStrictDerivAt.hasStrictFDerivAt_equiv
      (deriv_mulExp_ne_zero hw)
    exact ⟨h.toOpenPartialHomeomorph, h.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hs : IsLocalHomeomorph (Subtype.val : Regular → ℂ) :=
    (isOpen_ne : IsOpen {w : ℂ | w ≠ -1}).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact hm.comp hs.isLocalHomeomorphOn (fun w _ => w.property)

/-- Lifts of a continuous family of `C¹` paths vary continuously with the
parameter, provided all paths start at the same inverse value and avoid the
singular values. No continuity of the individually chosen lifts is assumed
in the family parameter. -/
theorem exists_continuous_inverse_family {A : Type*} [TopologicalSpace A]
    (γ : A → ℝ → ℂ) (hfamily : Continuous (fun p : unitInterval × A => γ p.2 p.1))
    (hsmooth : ∀ a, ContDiff ℝ 1 (γ a)) {z₀ w₀ : ℂ}
    (hstart : ∀ a, γ a 0 = z₀) (hw : mulExp w₀ = z₀)
    (hzero : ∀ a t, t ∈ Icc (0 : ℝ) 1 → γ a t ≠ 0)
    (hcrit : ∀ a t, t ∈ Icc (0 : ℝ) 1 → γ a t ≠ -Complex.exp (-1)) :
    ∃ F : A → ℂ, Continuous F ∧ (∀ a, mulExp (F a) = γ a 1) ∧
      ∀ a, (∀ t ∈ Icc (0 : ℝ) 1, γ a t = z₀) → F a = w₀ := by
  classical
  have hex (a : A) : ∃ F : unitInterval → ℂ, Continuous F ∧ F 0 = w₀ ∧
      ∀ t, mulExp (F t) = γ a t := by
    obtain ⟨F, hF, -⟩ := existsUnique_continuous_path_lift (by norm_num : (0 : ℝ) < 1)
      (hsmooth a) (hzero a) (hcrit a) (hw.trans (hstart a).symm)
    exact ⟨F, hF⟩
  choose F hFc hF0 hFi using hex
  have hn (a : A) (t : unitInterval) : F a t ≠ -1 := by
    intro he
    have hh := hFi a t
    rw [he, mulExp_neg_one] at hh
    exact hcrit a t t.property hh.symm
  let G : unitInterval × A → Regular := fun p => ⟨F p.2 p.1, hn p.2 p.1⟩
  have hG : Continuous G := by
    apply regularMulExp_localHomeomorph.continuous_lift
      (T2Space.isSeparatedMap regularMulExp) ⟨_, hfamily⟩
    · funext p; exact hFi p.2 p.1
    · exact (show Continuous (fun a => F a 0) from by
        simpa only [hF0] using (continuous_const : Continuous (fun _ : A => w₀))).subtype_mk _
    · intro a
      exact (hFc a).subtype_mk (hn a)
  refine ⟨fun a => (G (1, a)).val, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (hG.comp (continuous_const.prodMk continuous_id))
  · intro a; exact hFi a 1
  · intro a ha
    have he : F a = fun _ => w₀ := by
      apply eq_of_continuous_mulExp_lifts (hFc a) continuous_const
        (fun t => (hFi a t).trans ((ha t t.property).trans hw.symm))
        (fun t => by rw [hFi a t]; exact hcrit a t t.property) (t₀ := 0)
      exact hF0 a
    exact congrFun he 1

/-- A normalized analytic inverse exists on every open star-shaped domain
avoiding the two singular values. Straight-path lifts construct the function;
continuity of the family and local inverse uniqueness establish analyticity. -/
theorem exists_analytic_inverse_on_starDomain {D : Set ℂ} {z₀ w₀ : ℂ}
    (hopen : IsOpen D) (hstar : StarConvex ℝ z₀ D) (hz₀ : z₀ ∈ D)
    (hzero : ∀ z ∈ D, z ≠ 0) (hcrit : ∀ z ∈ D, z ≠ -Complex.exp (-1))
    (hw : mulExp w₀ = z₀) :
    ∃ W : ℂ → ℂ, AnalyticOnNhd ℂ W D ∧ W z₀ = w₀ ∧
      ∀ z ∈ D, mulExp (W z) = z := by
  classical
  let γ : D → ℝ → ℂ := fun z t => z₀ + (t : ℂ) * ((z : ℂ) - z₀)
  have hmem (z : D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ z t ∈ D := by
    simpa [γ, Complex.real_smul] using hstar.add_smul_mem (by simpa only [add_sub_cancel] using z.property) ht.1 ht.2
  obtain ⟨f, hf, hfi, hfbase⟩ := exists_continuous_inverse_family γ
    (by dsimp [γ]; fun_prop) (fun z => by
      have hcast : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
      exact contDiff_const.add (hcast.mul contDiff_const))
    (fun z => by simp [γ]) hw
    (fun z t ht => hzero _ (hmem z ht)) (fun z t ht => hcrit _ (hmem z ht))
  let W : ℂ → ℂ := fun z => if hz : z ∈ D then f ⟨z, hz⟩ else 0
  have hW (z : D) : W z = f z := by simp [W]
  have hcont : ContinuousOn W D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hf.congr (fun z => (hW z).symm)
  have hinv : ∀ z ∈ D, mulExp (W z) = z := by
    intro z hz
    rw [show W z = f ⟨z, hz⟩ from hW ⟨z, hz⟩, hfi]
    simp [γ]
  refine ⟨W, ?_, ?_, hinv⟩
  · intro z hz
    have he := hinv z hz
    have hn : W z ≠ -1 := by
      intro hn
      rw [hn, mulExp_neg_one] at he
      exact hcrit z hz he.symm
    obtain ⟨g, hg, hleft, hright⟩ := exists_analytic_localInverse hn
    rw [he] at hg
    have ht := (hcont z hz).continuousAt (hopen.mem_nhds hz)
    apply hg.congr
    filter_upwards [ht.tendsto.eventually hleft, hopen.mem_nhds hz] with y hy hyD
    rw [hinv y hyD] at hy
    exact hy
  · rw [show W z₀ = f ⟨z₀, hz₀⟩ from hW ⟨z₀, hz₀⟩]
    apply hfbase
    intro t ht
    simp [γ]

end LambertW.Complex
