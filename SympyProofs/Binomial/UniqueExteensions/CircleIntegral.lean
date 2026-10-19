module

public import SympyProofs.Binomial.Complex
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle-integral interpolations of the integer-lower binomial convention

For `0 < r < 1`, `circleIntegralChoose r z w` is the normalized integral, for `0 ≤ t ≤ 2π`,
of `exp (z * log (1 + r * exp (t * I)) - w * (log r + t * I))`.
The logarithm of `1 + r * exp (t * I)` stays on its principal analytic branch.
The second logarithm is explicitly unwrapped along the circle.

The radius and starting angle are parameters of this jointly entire interpolation.

`circleIntegralChoose_int_eq_choose` proves agreement for every complex upper argument and
every integer lower argument. `circleIntegralChoose_pascal` extends Pascal's identity to
both complex variables. `CircleUniqueness.lean` characterizes the interpolation by its
weighted Fourier spectrum and polynomial integer-lower slices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

attribute [local instance] Measure.Subtype.measureSpace

namespace SympyBinomial

/-- An admissible coefficient-extraction circle has radius strictly between zero and one. -/
abbrev InterpolationRadius := Set.Ioo (0 : ℝ) 1

/-- The circle-integral interpolation, using the angle interval `[0, 2π]` and radius `r`. -/
def circleIntegralChoose (r : InterpolationRadius) (z w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ in 0..2 * Real.pi,
    Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))

/-- The same circle construction with a specified starting angle. Different
angles agree at integer lower arguments but can differ elsewhere. -/
def angleCircleChoose (r : InterpolationRadius) (θ : ℝ) (z w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ in θ..θ + 2 * Real.pi,
    Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))

private theorem circle_one_add_mem_slitPlane (r : InterpolationRadius) (t : ℝ) :
    1 + circleMap 0 r t ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_of_norm_lt_one
  simpa only [norm_circleMap_zero, abs_of_pos r.property.1] using r.property.2

private theorem continuous_log_circle (r : InterpolationRadius) :
    Continuous (fun t : ℝ => Complex.log (1 + circleMap 0 r t)) := by
  have hc : Continuous (fun t : ℝ => 1 + circleMap 0 r t) := by fun_prop
  exact hc.clog (circle_one_add_mem_slitPlane r)

private def integralContinuousMap {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] :
    C(K, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

private theorem integralContinuousMap_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (f : C(K, ℂ)) :
    integralContinuousMap μ f = ∫ t, f t ∂μ := by
  change MeasureTheory.L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
  rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) μ f)

private theorem continuousMap_exp_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K, ℂ)) (t : K) : (NormedSpace.exp f) t = Complex.exp (f t) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t) (continuous_eval_const t) f

/-- Integrating exponentials of two bounded continuous coefficients is jointly entire. -/
private theorem analyticAt_integral_exp {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (a b : C(K, ℂ)) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => ∫ t, Complex.exp (q.1 * a t - q.2 * b t) ∂μ) p := by
  have h : AnalyticAt ℂ (fun q : ℂ × ℂ => NormedSpace.exp (q.1 • a - q.2 • b)) p :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp
      ((analyticAt_fst.smul analyticAt_const).sub (analyticAt_snd.smul analyticAt_const))
  have heq : (fun q : ℂ × ℂ => integralContinuousMap μ
      (NormedSpace.exp (q.1 • a - q.2 • b))) =
      (fun q : ℂ × ℂ => ∫ t, Complex.exp (q.1 * a t - q.2 * b t) ∂μ) := by
    funext q
    rw [integralContinuousMap_apply]
    congr 1
    funext t
    simp only [continuousMap_exp_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
  rw [← heq]
  exact ((integralContinuousMap μ).analyticAt _).comp h

/-- Joint analyticity holds at every point of `ℂ × ℂ`, including negative integer uppers. -/
theorem analyticAt_angleCircleChoose (r : InterpolationRadius) (θ : ℝ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => angleCircleChoose r θ q.1 q.2) p := by
  let K := Set.Icc θ (θ + 2 * Real.pi)
  have : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  let a : C(K, ℂ) := ⟨fun t => Complex.log (1 + circleMap 0 r t),
    (continuous_log_circle r).comp continuous_subtype_val⟩
  let b : C(K, ℂ) := ⟨fun t => Complex.log (r : ℂ) + (t : ℂ) * Complex.I,
    by fun_prop⟩
  have h := analyticAt_integral_exp (volume : Measure K) a b p
  have heq : (fun q : ℂ × ℂ => ∫ t : K, Complex.exp (q.1 * a t - q.2 * b t)) =
      (fun q : ℂ × ℂ => ∫ t : ℝ in θ..θ + 2 * Real.pi,
        Complex.exp (q.1 * Complex.log (1 + circleMap 0 r t) -
          q.2 * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))) := by
    funext q
    change (∫ t : Set.Icc θ (θ + 2 * Real.pi),
      Complex.exp (q.1 * Complex.log (1 + circleMap 0 r t) -
        q.2 * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))) = _
    rw [intervalIntegral.integral_of_le (show θ ≤ θ + 2 * Real.pi by linarith [Real.two_pi_pos]),
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact integral_subtype measurableSet_Icc (fun t : ℝ =>
      Complex.exp (q.1 * Complex.log (1 + circleMap 0 r t) -
        q.2 * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)))
  rw [heq] at h
  exact analyticAt_const.fun_mul h

/-- The original angle interval is the special case with starting angle zero. -/
theorem analyticAt_circleIntegralChoose (r : InterpolationRadius) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => circleIntegralChoose r q.1 q.2) p := by
  simpa only [angleCircleChoose, circleIntegralChoose, zero_add] using
    analyticAt_angleCircleChoose r 0 p

/-- The interpolation is entire as a function of both complex arguments together. -/
theorem analyticOnNhd_circleIntegralChoose (r : InterpolationRadius) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => circleIntegralChoose r p.1 p.2) Set.univ :=
  fun p _ => analyticAt_circleIntegralChoose r p

private theorem exp_circle_log (r : InterpolationRadius) (t : ℝ) :
    Complex.exp (Complex.log (r : ℂ) + (t : ℂ) * Complex.I) = circleMap 0 r t := by
  rw [Complex.exp_add, Complex.exp_log (by exact_mod_cast r.property.1.ne')]
  exact (circleMap_zero r t).symm

private theorem circleIntegralChoose_integrand_int (r : InterpolationRadius) (z : ℂ) (k : ℤ)
    (t : ℝ) :
    Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      (k : ℂ) * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)) =
      circleMap 0 r t ^ (-k) * (1 + circleMap 0 r t) ^ z := by
  rw [Complex.exp_sub, Complex.exp_int_mul, exp_circle_log,
    Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (circle_one_add_mem_slitPlane r t)),
    zpow_neg]
  simp only [div_eq_mul_inv, mul_comm]

/-- At integer lower arguments the unwrapped integral is a Cauchy coefficient integral. -/
theorem circleIntegralChoose_int_eq_circleIntegral (r : InterpolationRadius) (z : ℂ) (k : ℤ) :
    circleIntegralChoose r z (k : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ t in C(0, (r : ℝ)), t ^ (-k - 1) * (1 + t) ^ z := by
  have hi : (∮ t in C(0, (r : ℝ)), t ^ (-k - 1) * (1 + t) ^ z) =
      Complex.I * ∫ t : ℝ in 0..2 * Real.pi,
        Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
          (k : ℂ) * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [deriv_circleMap, smul_eq_mul, circleIntegralChoose_integrand_int]
    have hc : circleMap 0 r t ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simpa only [norm_circleMap_zero, abs_of_pos r.property.1] using r.property.1.ne'
    have hp : circleMap 0 r t ^ (-k - 1) * circleMap 0 r t = circleMap 0 r t ^ (-k) := by
      simpa only [sub_add_cancel, zpow_one] using (zpow_add₀ hc (-k - 1) 1).symm
    calc
      _ = Complex.I * (circleMap 0 r t ^ (-k - 1) * circleMap 0 r t) *
          (1 + circleMap 0 r t) ^ z := by ring
      _ = _ := by rw [hp]; ring
  rw [hi]
  simp only [circleIntegralChoose, mul_inv_rev]
  calc
    _ = (Complex.I⁻¹ * Complex.I) * (2 * Real.pi : ℂ)⁻¹ *
        (∫ t : ℝ in 0..2 * Real.pi,
          Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
            (k : ℂ) * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))) := by
      rw [inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
      rw [mul_inv_rev]
    _ = _ := by ring

private theorem differentiableOn_one_add_cpow (r : InterpolationRadius) (z : ℂ) :
    DifferentiableOn ℂ (fun t : ℂ => (1 + t) ^ z) (Metric.closedBall 0 (r : ℝ)) := by
  intro t ht
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.cpow_const (by fun_prop)
  apply Complex.mem_slitPlane_of_norm_lt_one
  have ht' : ‖t‖ ≤ (r : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  exact ht'.trans_lt r.property.2

/-- For nonnegative integer lower arguments, coefficient extraction gives the binomial polynomial. -/
theorem circleIntegralChoose_nat_eq_choose (r : InterpolationRadius) (z : ℂ) (k : ℕ) :
    circleIntegralChoose r z (k : ℂ) = choose z (k : ℤ) := by
  let R : NNReal := ⟨r, r.property.1.le⟩
  have hR : 0 < R := r.property.1
  have hseries := (differentiableOn_one_add_cpow r z).hasFPowerSeriesOnBall (R := R) hR
  have heq := hseries.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := z))
  have hcoeff := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s k (fun _ => 1)) heq
  simp only [cauchyPowerSeries_apply, binomialSeries_apply, List.prod_ofFn, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_pow, smul_eq_mul, mul_one, sub_zero,
    one_div] at hcoeff
  rw [show (k : ℂ) = ((k : ℤ) : ℂ) by simp, circleIntegralChoose_int_eq_circleIntegral, choose_natCast]
  convert hcoeff using 2
  congr 1
  funext t
  rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega]
  simp only [zpow_neg, zpow_natCast, pow_succ, mul_inv_rev]
  ring

private theorem circleIntegralChoose_negSucc_eq_zero (r : InterpolationRadius) (z : ℂ) (k : ℕ) :
    circleIntegralChoose r z (Int.negSucc k : ℂ) = 0 := by
  rw [circleIntegralChoose_int_eq_circleIntegral]
  have hk : -Int.negSucc k - 1 = (k : ℤ) := by omega
  simp only [hk, zpow_natCast]
  have hd : DifferentiableOn ℂ (fun t : ℂ => t ^ k * (1 + t) ^ z)
      (Metric.closedBall 0 (r : ℝ)) :=
    (differentiableOn_id.pow k).fun_mul (differentiableOn_one_add_cpow r z)
  rw [(hd.diffContOnCl_ball (Subset.rfl)).circleIntegral_eq_zero r.property.1.le,
    mul_zero]

/-- Agreement with every integer-lower slice for every complex upper argument, with no exceptions. -/
@[simp]
theorem circleIntegralChoose_int_eq_choose (r : InterpolationRadius) (z : ℂ) (k : ℤ) :
    circleIntegralChoose r z (k : ℂ) = choose z k := by
  cases k with
  | ofNat k => exact circleIntegralChoose_nat_eq_choose r z k
  | negSucc k =>
    rw [circleIntegralChoose_negSucc_eq_zero, choose_of_neg _ (by omega)]

/-- In particular, the entire interpolation matches SymPy's whole integer lattice. -/
@[simp]
theorem circleIntegralChoose_intCast_intCast (r : InterpolationRadius) (n k : ℤ) :
    circleIntegralChoose r (n : ℂ) (k : ℂ) = ((choose n k : ℤ) : ℂ) := by
  rw [circleIntegralChoose_int_eq_choose, intCast_choose]

/-- Integer lower arguments make the integrand periodic, so the starting
angle does not affect any integer-lower slice. -/
theorem angleCircleChoose_int_eq_choose (r : InterpolationRadius) (θ : ℝ)
    (z : ℂ) (k : ℤ) : angleCircleChoose r θ z (k : ℂ) = choose z k := by
  have hp : Function.Periodic (fun t : ℝ =>
      Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
        (k : ℂ) * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))) (2 * Real.pi) := by
    intro t
    dsimp only
    rw [circleIntegralChoose_integrand_int, circleIntegralChoose_integrand_int,
      periodic_circleMap 0 r t]
  have heq : angleCircleChoose r θ z (k : ℂ) = circleIntegralChoose r z (k : ℂ) := by
    unfold angleCircleChoose circleIntegralChoose
    congr 1
    simpa only [zero_add] using hp.intervalIntegral_add_eq θ 0
  exact heq.trans (circleIntegralChoose_int_eq_choose r z k)

private theorem continuous_circleIntegralChoose_integrand (r : InterpolationRadius) (z w : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))) := by
  have h := continuous_log_circle r
  fun_prop

/-- The integral family also satisfies Pascal's recurrence for complex lower arguments. -/
theorem angleCircleChoose_add_one_add_one (r : InterpolationRadius) (θ : ℝ) (z w : ℂ) :
    angleCircleChoose r θ (z + 1) (w + 1) = angleCircleChoose r θ z w + angleCircleChoose r θ z (w + 1) := by
  simp only [angleCircleChoose, ← mul_add]
  rw [← intervalIntegral.integral_add
    ((continuous_circleIntegralChoose_integrand r z w).intervalIntegrable _ _)
    ((continuous_circleIntegralChoose_integrand r z (w + 1)).intervalIntegrable _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  let a := Complex.log (1 + circleMap 0 r t)
  let b := Complex.log (r : ℂ) + (t : ℂ) * Complex.I
  change Complex.exp ((z + 1) * a - (w + 1) * b) =
    Complex.exp (z * a - w * b) + Complex.exp (z * a - (w + 1) * b)
  rw [show (z + 1) * a - (w + 1) * b = a + (z * a - (w + 1) * b) by ring,
    show z * a - w * b = b + (z * a - (w + 1) * b) by ring,
    Complex.exp_add, Complex.exp_add]
  have ha : Complex.exp a = 1 + circleMap 0 r t :=
    Complex.exp_log (Complex.slitPlane_ne_zero (circle_one_add_mem_slitPlane r t))
  have hb : Complex.exp b = circleMap 0 r t := exp_circle_log r t
  rw [ha, hb]
  ring

/-- The original angle-zero family satisfies Pascal. -/
theorem circleIntegralChoose_add_one_add_one (r : InterpolationRadius) (z w : ℂ) :
    circleIntegralChoose r (z + 1) (w + 1) =
      circleIntegralChoose r z w + circleIntegralChoose r z (w + 1) := by
  simpa only [angleCircleChoose, circleIntegralChoose, zero_add] using
    angleCircleChoose_add_one_add_one r 0 z w

/-- Pascal's identity holds everywhere for this entire interpolation. -/
theorem circleIntegralChoose_pascal (r : InterpolationRadius) (z w : ℂ) :
    circleIntegralChoose r z w = circleIntegralChoose r (z - 1) w + circleIntegralChoose r (z - 1) (w - 1) := by
  simpa [add_comm] using circleIntegralChoose_add_one_add_one r (z - 1) (w - 1)

/-- Every fixed starting angle preserves the complex Pascal identity. -/
theorem angleCircleChoose_pascal (r : InterpolationRadius) (θ : ℝ) (z w : ℂ) :
    angleCircleChoose r θ z w =
      angleCircleChoose r θ (z - 1) w + angleCircleChoose r θ (z - 1) (w - 1) := by
  simpa [add_comm] using angleCircleChoose_add_one_add_one r θ (z - 1) (w - 1)

end SympyBinomial
