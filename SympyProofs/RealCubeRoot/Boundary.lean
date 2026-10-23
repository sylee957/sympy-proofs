module

public import SympyProofs.RealCubeRoot.Uniqueness
public import SympyProofs.RealCubeRoot.Extensions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Right-side and left-side boundary conventions

Both total extensions commute with conjugation, restrict to the same analytic
branch, and are continuous on their respective closed half-planes. They are
also continuous at zero and along the imaginary axis. Choosing a side fixes
the total extension uniquely, but the two choices differ at `I`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Filter
open scoped ComplexConjugate Topology

theorem isRealBranch_cubicSurdRight : IsRealBranch cubicSurdRight where
  cube z _ := cubicSurdRight_cube z
  analytic := analyticOnNhd_cubicSurdRight
  conjugation z _ := cubicSurdRight_conj z

theorem isRealBranch_cubicSurdLeft : IsRealBranch cubicSurdLeft where
  cube z _ := cubicSurdLeft_cube z
  analytic := analyticOnNhd_cubicSurdLeft
  conjugation z _ := cubicSurdLeft_conj z

theorem cubicSurdLeft_eqOn_cubicSurdRight : Set.EqOn cubicSurdLeft cubicSurdRight domain :=
  isRealBranch_cubicSurdLeft.eqOn isRealBranch_cubicSurdRight

/-- Continuity from the right, including all boundary points and zero. -/
theorem continuousOn_cubicSurdRight_closedHalfPlane :
    ContinuousOn cubicSurdRight {z : ℂ | 0 ≤ z.re} := by
  intro z hz
  exact (continuousAt_principal_of_re_nonneg hz).continuousWithinAt.congr_of_mem
    (fun _ hw => cubicSurdRight_eq_principal hw) hz

/-- Continuity from the left, including all boundary points and zero. -/
theorem continuousOn_cubicSurdLeft_closedHalfPlane :
    ContinuousOn cubicSurdLeft {z : ℂ | z.re ≤ 0} := by
  intro z hz
  have hp := continuousAt_principal_of_re_nonneg (z := -z) (by simpa using neg_nonneg.mpr hz)
  have hc : ContinuousAt (fun w : ℂ => -principal (-w)) z :=
    (hp.comp continuousAt_id.neg).neg
  exact hc.continuousWithinAt.congr_of_mem (fun _ hw => cubicSurdLeft_eq_neg_principal hw) hz

/-- At a cut point, approach from the closed right half-plane. -/
theorem continuousWithinAt_cubicSurdRight_axis {z : ℂ} (hz : z.re = 0) :
    ContinuousWithinAt cubicSurdRight {w : ℂ | 0 ≤ w.re} z :=
  continuousOn_cubicSurdRight_closedHalfPlane z hz.ge

/-- At a cut point, approach from the closed left half-plane. -/
theorem continuousWithinAt_cubicSurdLeft_axis {z : ℂ} (hz : z.re = 0) :
    ContinuousWithinAt cubicSurdLeft {w : ℂ | w.re ≤ 0} z :=
  continuousOn_cubicSurdLeft_closedHalfPlane z hz.le

/-- The right-side limit along the open half-plane gives the assigned value. -/
theorem tendsto_cubicSurdRight_from_right {z : ℂ} (hz : z.re = 0) :
    Tendsto cubicSurdRight (𝓝[{w : ℂ | 0 < w.re}] z) (𝓝 (cubicSurdRight z)) :=
  (continuousWithinAt_cubicSurdRight_axis hz).mono (by intro w hw; change 0 ≤ w.re; exact le_of_lt hw)

/-- The left-side limit along the open half-plane gives the assigned value. -/
theorem tendsto_cubicSurdLeft_from_left {z : ℂ} (hz : z.re = 0) :
    Tendsto cubicSurdLeft (𝓝[{w : ℂ | w.re < 0}] z) (𝓝 (cubicSurdLeft z)) :=
  (continuousWithinAt_cubicSurdLeft_axis hz).mono (by intro w hw; change w.re ≤ 0; exact le_of_lt hw)

/-- Restricting to the cut itself gives a continuous function. -/
theorem continuousOn_cubicSurdRight_axis : ContinuousOn cubicSurdRight {z : ℂ | z.re = 0} :=
  continuousOn_cubicSurdRight_closedHalfPlane.mono (fun _ hz => hz.ge)

theorem continuousOn_cubicSurdLeft_axis : ContinuousOn cubicSurdLeft {z : ℂ | z.re = 0} :=
  continuousOn_cubicSurdLeft_closedHalfPlane.mono (fun _ hz => hz.le)

/-- At zero the two pieces have the same limit, so continuity is two-sided. -/
theorem continuousAt_cubicSurdRight_zero : ContinuousAt cubicSurdRight 0 := by
  have hp : ContinuousAt principal 0 := continuousAt_principal_of_re_nonneg (by simp)
  have hp' : Tendsto principal (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa [ContinuousAt, principal] using hp
  have hn : Tendsto (fun w : ℂ => -w) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [Pi.neg_def, id_eq, neg_zero] using
      (continuousAt_id (x := (0 : ℂ))).neg.tendsto
  have hn' : Tendsto (fun w : ℂ => -principal (-w)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using (hp'.comp hn).neg
  change Tendsto cubicSurdRight (𝓝 0) (𝓝 (cubicSurdRight 0))
  rw [show cubicSurdRight 0 = 0 from cubicSurdRight_zero]
  exact hn'.if' (p := fun z : ℂ => z.re < 0) hp'

theorem continuousAt_cubicSurdLeft_zero : ContinuousAt cubicSurdLeft 0 := by
  have hp : ContinuousAt cubicSurdRight (-(0 : ℂ)) := by
    simpa using continuousAt_cubicSurdRight_zero
  exact (hp.comp (f := fun z : ℂ => -z) (x := 0) continuousAt_id.neg).neg

/-- Once the right-side continuity convention is required, the total extension is unique. -/
theorem unique_cubicSurdRight {f : ℂ → ℂ} (hf : IsRealBranch f)
    (hc : ContinuousOn f {z : ℂ | 0 ≤ z.re}) : f = cubicSurdRight := by
  have h := hf.eqOn isRealBranch_cubicSurdRight
  have hr : Set.EqOn f cubicSurdRight {z : ℂ | 0 < z.re} :=
    fun _ hz => h (Or.inl (ne_of_gt hz))
  have hclosed := hr.of_subset_closure hc continuousOn_cubicSurdRight_closedHalfPlane
    (by intro w hw; change 0 ≤ w.re; exact le_of_lt hw)
    (by rw [closure_setOfPred_lt_re])
  funext z
  by_cases hz : 0 ≤ z.re
  · exact hclosed hz
  · exact h (Or.inl (ne_of_lt (lt_of_not_ge hz)))

/-- Once the left-side continuity convention is required, the total extension is unique. -/
theorem unique_cubicSurdLeft {f : ℂ → ℂ} (hf : IsRealBranch f)
    (hc : ContinuousOn f {z : ℂ | z.re ≤ 0}) : f = cubicSurdLeft := by
  have h := hf.eqOn isRealBranch_cubicSurdLeft
  have hl : Set.EqOn f cubicSurdLeft {z : ℂ | z.re < 0} :=
    fun _ hz => h (Or.inl (ne_of_lt hz))
  have hclosed := hl.of_subset_closure hc continuousOn_cubicSurdLeft_closedHalfPlane
    (by intro w hw; change w.re ≤ 0; exact le_of_lt hw)
    (by rw [closure_setOfPred_re_lt])
  funext z
  by_cases hz : z.re ≤ 0
  · exact hclosed hz
  · exact h (Or.inl (ne_of_gt (lt_of_not_ge hz)))

private theorem cubicSurdRight_I_re_pos : 0 < (cubicSurdRight I).re := by
  rw [cubicSurdRight_eq_principal (by simp)]
  have h := Complex.cpow_ofReal_re I (3⁻¹ : ℝ)
  simp only [Complex.ofReal_inv, Complex.ofReal_ofNat, norm_I, Real.one_rpow,
    one_mul, arg_I] at h
  rw [principal, h]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> norm_num <;> linarith [Real.pi_pos]

/-- The two allowed total functions make different choices at the cut point `I`. -/
theorem cubicSurdLeft_I_ne_cubicSurdRight : cubicSurdLeft I ≠ cubicSurdRight I := by
  intro h
  have hc : cubicSurdRight (-I) = conj (cubicSurdRight I) := by
    simpa using cubicSurdRight_conj I
  have hr := congrArg Complex.re h
  simp only [cubicSurdLeft, hc, neg_re, conj_re] at hr
  linarith [cubicSurdRight_I_re_pos]

/-- Global algebraic laws and analyticity on `analyticDomain` do not uniquely determine
the values outside `domain`, even when every real value is prescribed. -/
theorem total_extension_not_unique :
    ∃ f g : ℂ → ℂ,
      IsRealBranch f ∧ IsRealBranch g ∧
      (∀ z, f z ^ 3 = z) ∧ (∀ z, g z ^ 3 = z) ∧
      (∀ z, f (conj z) = conj (f z)) ∧ (∀ z, g (conj z) = conj (g z)) ∧
      (∀ x : ℝ, f x = (realCubicSurd x : ℂ)) ∧
      (∀ x : ℝ, g x = (realCubicSurd x : ℂ)) ∧ f ≠ g := by
  refine ⟨cubicSurdLeft, cubicSurdRight, isRealBranch_cubicSurdLeft, isRealBranch_cubicSurdRight,
    cubicSurdLeft_cube, cubicSurdRight_cube, cubicSurdLeft_conj, cubicSurdRight_conj,
    cubicSurdLeft_ofReal, cubicSurdRight_ofReal, ?_⟩
  intro h
  exact cubicSurdLeft_I_ne_cubicSurdRight (congrFun h I)

end RealCubeRoot
