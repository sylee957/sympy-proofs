import SympyProofs.LambertW.Complex.Branches.Comparison
import SympyProofs.LambertW.Complex.Branches.Conjugation
import SympyProofs.LambertW.Complex.Branches.Definitions
import SympyProofs.LambertW.Complex.Middle.Conjugation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Comparison of the double-cut middle branch with indexed W₋₁

An explicit path in the inverse plane connects the real lower normalization
at `-2` to the indexed normalization at `-3πi/2`. Its forward image stays
in the upper half-plane except at the two endpoints.
-/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

private theorem inverse_along_curve {S : Set ℝ} (hS : IsPreconnected S)
    {U : Set ℂ} {W : ℂ → ℂ} (hW : AnalyticOnNhd ℂ W U)
    (hi : ∀ z ∈ U, mulExp (W z) = z)
    (hn : ∀ z ∈ U, z ≠ -Complex.exp (-1))
    {f : ℝ → ℂ} (hf : Continuous f) (hdom : ∀ t ∈ S, mulExp (f t) ∈ U)
    {a : ℝ} (ha : a ∈ S) (hstart : W (mulExp (f a)) = f a) :
    ∀ t ∈ S, W (mulExp (f t)) = f t := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hfc : Continuous (fun t : S => f t) := hf.comp continuous_subtype_val
  have hmc : Continuous (fun t : S => mulExp (f t)) :=
    (continuous_iff_continuousAt.mpr (fun z => (analyticAt_mulExp z).continuousAt)).comp hfc
  have hwc : Continuous (fun t : S => W (mulExp (f t))) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hW _ (hdom t t.property)).continuousAt.comp
        (f := fun t : S => mulExp (f t)) hmc.continuousAt)
  have he := eq_of_continuous_mulExp_lifts hwc hfc
    (fun t => hi _ (hdom t t.property))
    (fun t => by rw [hi _ (hdom t t.property)]; exact hn _ (hdom t t.property))
    (t₀ := ⟨a, ha⟩) hstart
  intro t ht
  exact congrFun he ⟨t, ht⟩

private theorem vertical_image_pos {t : ℝ} (ht : t ∈ Ioc 0 Real.pi) :
    0 < (mulExp (-2 - (t : ℂ) * Complex.I)).im := by
  rw [mulExp_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  apply mul_pos (Real.exp_pos _)
  by_cases htpi : t = Real.pi
  · subst t; simp [Real.pi_pos]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_of_le_of_ne ht.2 htpi)
  by_cases hh : t ≤ Real.pi / 2
  · have hsbound := Real.mul_le_sin (le_of_lt ht.1) hh
    have hcos := Real.cos_le_one t
    have hp := Real.pi_pos
    have hp4 := Real.pi_lt_four
    have hcoef : 1 < 4 / Real.pi := (lt_div_iff₀ hp).mpr (by simpa using hp4)
    have hprod := mul_lt_mul_of_pos_right hcoef ht.1
    have he : 4 / Real.pi = 2 * (2 / Real.pi) := by ring
    rw [he] at hprod
    have hb : t * Real.cos t ≤ t := by nlinarith
    nlinarith
  · have hc := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_ge hh)
      (show t ≤ Real.pi + Real.pi / 2 by linarith [ht.2, Real.pi_pos])
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht.1) hc]

private theorem middle_vertical_end :
    middle (mulExp (-2 - (Real.pi : ℂ) * Complex.I)) = -2 - (Real.pi : ℂ) * Complex.I := by
  have hcast : mulExp (-2) = (Real.mulExp (-2) : ℂ) := by
    simpa using mulExp_ofReal (-2)
  have hreal : Real.mulExp (-2) ∈ Ioo (-Real.exp (-1)) 0 := by
    constructor
    · have h := Real.strictAntiOn_mulExp (show (-2 : ℝ) ∈ Iic (-1) by norm_num)
        (show (-1 : ℝ) ∈ Iic (-1) by simp) (by norm_num : (-2 : ℝ) < -1)
      simpa using h
    · exact Real.mulExp_neg_of_le_neg_one (by norm_num)
  apply inverse_along_curve isPreconnected_Icc analyticOnNhd_middle
    (fun _ hz => mulExp_middle hz) (fun _ hz => middleDomain_ne_criticalValue hz)
    (S := Icc 0 Real.pi) (f := fun t : ℝ => -2 - (t : ℂ) * Complex.I) (by fun_prop) ?_
    (a := 0) (by simp [Real.pi_pos.le]) ?_ Real.pi (by simp [Real.pi_pos.le])
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      simpa only [Complex.ofReal_zero, zero_mul, sub_zero, hcast] using
        ofReal_mem_middleDomain.mpr hreal
    · exact Or.inl (ne_of_gt (vertical_image_pos ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩))
  · simpa only [Complex.ofReal_zero, zero_mul, sub_zero, hcast,
      Complex.ofReal_neg, Complex.ofReal_ofNat] using (middle_ofReal hreal).trans
      (congrArg (fun x : ℝ => (x : ℂ)) (Real.lower_mulExp (by norm_num : (-2 : ℝ) ≤ -1)))

private theorem middle_at_pi_I :
    middle (mulExp (-(Real.pi : ℂ) * Complex.I)) = -(Real.pi : ℂ) * Complex.I := by
  have hh := inverse_along_curve isPreconnected_Icc analyticOnNhd_middle
    (fun _ hz => mulExp_middle hz) (fun _ hz => middleDomain_ne_criticalValue hz)
    (f := fun a : ℝ => (a : ℂ) - (Real.pi : ℂ) * Complex.I) (by fun_prop)
    (S := Icc (-2) 0) ?_ (a := -2) (by norm_num) ?_ 0 (by norm_num)
  · simpa using hh
  · intro a ha
    apply Or.inl
    apply ne_of_gt
    rw [mulExp_im]
    simp [Complex.mul_re, Complex.mul_im, Real.pi_pos, Real.exp_pos]
  · simpa using middle_vertical_end

private theorem minusOne_at_pi_I :
    (branch (-1)) (mulExp (-(Real.pi : ℂ) * Complex.I)) = -(Real.pi : ℂ) * Complex.I := by
  have hvalue : -((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I = (negativeBranchValue 0) := by
    simp [negativeBranchValue, branchRadius]
  have hh := inverse_along_curve isPreconnected_Icc (analyticOnNhd_branch (-1))
    (fun _ hz => (mulExp_branch (-1)) hz) (fun _ hz => branchDomain_ne_criticalValue hz)
    (f := fun t : ℝ => -(t : ℂ) * Complex.I) (by fun_prop)
    (S := Icc Real.pi (3 * Real.pi / 2)) ?_ (a := 3 * Real.pi / 2)
    (by constructor <;> linarith [Real.pi_pos]) ?_ Real.pi
    (by constructor <;> linarith [Real.pi_pos])
  · exact hh
  · intro t ht
    by_cases he : t = 3 * Real.pi / 2
    · subst t
      rw [hvalue, (mulExp_negativeBranchValue 0)]
      exact (negativeBranchSeed 0).mem_domain
    · apply Or.inr
      apply ne_of_gt
      rw [mulExp_im]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      have hc := Real.cos_neg_of_pi_div_two_lt_of_lt
        (show Real.pi / 2 < t by linarith [ht.1, Real.pi_pos]) (show t < Real.pi + Real.pi / 2 by
          have hh := lt_of_le_of_ne ht.2 he
          linarith)
      nlinarith [mul_neg_of_pos_of_neg (show 0 < t by linarith [ht.1, Real.pi_pos]) hc]
  · rw [hvalue, (mulExp_negativeBranchValue 0), (show branch (-1) (branchRadius 0) = negativeBranchValue 0 from branch_negSucc_base 0)]

/-- The double-cut real-lower extension is the indexed branch W₋₁
throughout the upper half-plane. -/
theorem middle_eq_branch_neg_one_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    middle z = (branch (-1)) z := by
  let H : Set ℂ := {z | 0 < z.im}
  have hconv : Convex ℝ H := by
    intro a ha b hb s t hs ht hst
    change 0 < (s • a + t • b).im
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    change 0 < a.im at ha
    change 0 < b.im at hb
    by_cases hs0 : s = 0
    · have ht1 : t = 1 := by linarith
      simpa [hs0, ht1] using hb
    · nlinarith [mul_pos (lt_of_le_of_ne hs (Ne.symm hs0)) ha,
        mul_nonneg ht (le_of_lt hb)]
  let : PreconnectedSpace H := Subtype.preconnectedSpace hconv.isPreconnected
  have hcL : Continuous (fun t : H => middle t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticOnNhd_middle _ (Or.inl (ne_of_gt t.property))).continuousAt.comp
        continuous_subtype_val.continuousAt)
  have hcM : Continuous (fun t : H => (branch (-1)) t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      ((analyticOnNhd_branch (-1)) _ (Or.inr (ne_of_gt t.property))).continuousAt.comp
        continuous_subtype_val.continuousAt)
  have hbase : mulExp (-(Real.pi : ℂ) * Complex.I) ∈ H := by
    change 0 < (mulExp _).im
    rw [mulExp_im]
    simp [Complex.mul_re, Complex.mul_im, Real.pi_pos]
  have he := eq_of_continuous_mulExp_lifts hcL hcM
    (fun t => (mulExp_middle (Or.inl (ne_of_gt t.property))).trans
      ((mulExp_branch (-1)) (Or.inr (ne_of_gt t.property))).symm)
    (fun t => by
      rw [mulExp_middle (Or.inl (ne_of_gt t.property))]
      exact middleDomain_ne_criticalValue (Or.inl (ne_of_gt t.property)))
    (t₀ := ⟨_, hbase⟩) (middle_at_pi_I.trans minusOne_at_pi_I.symm)
  exact congrFun he ⟨z, hz⟩

/-- Equality of the two branches as functions restricted to the upper half-plane. -/
theorem eqOn_middle_minusOne_upper : EqOn middle (branch (-1)) {z : ℂ | 0 < z.im} :=
  fun _ hz => middle_eq_branch_neg_one_of_im_pos hz

/-- Below the real axis, the double-cut branch is the conjugate reflection
of the indexed branch, rather than the same indexed function. -/
theorem middle_eq_conj_minusOne_conj_of_im_neg {z : ℂ} (hz : z.im < 0) :
    middle z = starRingEnd ℂ ((branch (-1)) (starRingEnd ℂ z)) := by
  have hpos : 0 < (starRingEnd ℂ z).im := by simpa using hz
  have he := middle_eq_branch_neg_one_of_im_pos hpos
  rw [middle_conj (Or.inl (ne_of_lt hz))] at he
  have hh := congrArg (starRingEnd ℂ) he
  simpa using hh

/-- The real lower branch is the upper boundary value of indexed W₋₁
on the full interval `(-1/e, 0)`. -/
theorem tendsto_minusOne_upper_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (Real.lower x : ℂ)) := by
  have ht := (analyticOnNhd_middle _ (ofReal_mem_middleDomain.mpr hx)).continuousAt.tendsto
  rw [middle_ofReal hx] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact middle_eq_branch_neg_one_of_im_pos hz

/-- Below the real axis, the middle branch is the indexed branch of index +1. -/
theorem middle_eq_branch_one_of_im_neg {z : ℂ} (hz : z.im < 0) :
    middle z = branch 1 z := by
  have hd : conj z ∈ branchDomain :=
    (conj_mem_branchDomain z).mpr (Or.inr (ne_of_lt hz))
  have he := branch_natSucc_conj 0 hd
  change branch 1 (conj (conj z)) = conj (branch (-1) (conj z)) at he
  have he' : branch 1 z = conj (branch (-1) (conj z)) := by simpa using he
  rw [middle_eq_conj_minusOne_conj_of_im_neg hz, he']

end LambertW.Complex
