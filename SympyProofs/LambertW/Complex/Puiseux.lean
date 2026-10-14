import SympyProofs.LambertW.Complex.SquareRoot
import SympyProofs.LambertW.Complex.TaylorCoefficients
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Convergent square-root expansion at the principal branch point

`exists_principal_puiseux_expansion` gives
`W = -1 + p - p²/3 + 11p³/72 + p⁴R(p)` with an analytic remainder.
The parameter satisfies `p² = 2e(z + 1/e)` and is normalized by a coordinate
`P` with `P(0) = 0`, `P'(0) = 1`, applied to `W + 1`. This formulation
keeps the sign consistent with either boundary convention.

`exists_convergent_puiseux_inverse` also proves convergence of the full
local series in the square-root parameter; only its cubic coefficients
are computed explicitly here.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- The normalized forward map in the displacement `u = W + 1`. -/
noncomputable def branchSeries (u : ℂ) : ℂ := 2 * ((u - 1) * Complex.exp u + 1)

theorem analyticAt_branchSeries (u : ℂ) : AnalyticAt ℂ branchSeries u := by
  unfold branchSeries; fun_prop

@[simp] theorem branchSeries_zero : branchSeries 0 = 0 := by simp [branchSeries]

theorem branchSeries_eq (u : ℂ) :
    branchSeries u = 2 * Complex.exp 1 * (mulExp (u - 1) - mulExp (-1)) := by
  simp only [branchSeries, mulExp, Complex.exp_sub, sub_neg_eq_add, neg_mul]
  rw [Complex.exp_neg]
  field_simp

theorem iteratedDeriv_branchSeries (n : ℕ) :
    iteratedDeriv (n + 1) branchSeries = fun u => 2 * Complex.exp u * (u + n) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext u
    have h := (((hasDerivAt_id u).sub_const 1).fun_mul (Complex.hasDerivAt_exp u)).add_const 1
    have hd : HasDerivAt branchSeries (2 * Complex.exp u * u) u := by
      convert h.const_mul 2 using 1
      · rfl
      · dsimp; ring
    simpa using hd.deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have h := ((Complex.hasDerivAt_exp u).const_mul 2).fun_mul
      ((hasDerivAt_id u).add_const (n : ℂ))
    convert h.deriv using 1 <;> dsimp
    push_cast
    ring

/-- Normalized forward expansion through degree four. -/
theorem exists_branchSeries_quartic_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ u,
      branchSeries u = u ^ 2 + (2 / 3 : ℂ) * u ^ 3 + (1 / 4 : ℂ) * u ^ 4 + u ^ 5 * R u := by
  obtain ⟨R, hR, h⟩ := (analyticAt_branchSeries 0).exists_eq_sum_add_pow_mul 5
  refine ⟨R, hR, fun u => ?_⟩
  have hd0 : deriv branchSeries 0 = 0 := by
    have hh := congrFun (iteratedDeriv_branchSeries 0) 0
    simpa [iteratedDeriv_one] using hh
  have hu := h u
  norm_num [Nat.choose, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_branchSeries, smul_eq_mul, hd0] at hu
  convert hu using 1; ring

/-- There is an analytic coordinate `P` with `P'(0)=1` whose square is the
normalized forward map. It admits an analytic local inverse `Q`. -/
theorem exists_puiseux_coordinates :
    ∃ P Q : ℂ → ℂ, AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ Q 0 ∧
      P 0 = 0 ∧ Q 0 = 0 ∧ HasDerivAt P 1 0 ∧ HasDerivAt Q 1 0 ∧
      (∀ u, P u ^ 2 = branchSeries u) ∧
      (∀ᶠ u in 𝓝 0, Q (P u) = u) ∧ (∀ᶠ p in 𝓝 0, P (Q p) = p) := by
  obtain ⟨g, hg, hg0, he⟩ := exists_mulExp_branchPoint_factor
  let H : ℂ → ℂ := fun u => 2 * Complex.exp 1 * g u
  have hH : AnalyticAt ℂ H 0 := analyticAt_const.mul hg
  have hH0 : H 0 = 1 := by
    dsimp [H]; rw [hg0, Complex.exp_neg]; field_simp
  have hsqrt : AnalyticAt ℂ Complex.sqrt (H 0) := by
    rw [hH0]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  let P : ℂ → ℂ := fun u => u * Complex.sqrt (H u)
  have hP : AnalyticAt ℂ P 0 := analyticAt_id.fun_mul (hsqrt.fun_comp hH)
  have hP0 : P 0 = 0 := by simp [P]
  have hdP : HasDerivAt P 1 0 := by
    convert (hasDerivAt_id (0 : ℂ)).fun_mul (hsqrt.fun_comp hH).differentiableAt.hasDerivAt using 1 <;> simp [P, hH0]
  have hn : deriv P 0 ≠ 0 := by rw [hdP.deriv]; norm_num
  let Q := hP.hasStrictDerivAt.localInverse P (deriv P 0) 0 hn
  have hQ : AnalyticAt ℂ Q 0 := by simpa [Q, hP0] using hP.analyticAt_localInverse hn
  have hleft : ∀ᶠ u in 𝓝 0, Q (P u) = u := hP.hasStrictDerivAt.eventually_left_inverse hn
  have hQ0 : Q 0 = 0 := by simpa [hP0] using hleft.self_of_nhds
  have hdQ : HasDerivAt Q 1 0 := by
    simpa [Q, hP0, hdP.deriv] using (hP.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  refine ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, ?_, hleft, ?_⟩
  · intro u
    dsimp [P]
    rw [mul_pow, Complex.sqrt, Complex.cpow_ofNat_inv_pow]
    rw [branchSeries_eq, he]
    dsimp [H]
    ring
  · simpa [Q, hP0] using hP.hasStrictDerivAt.eventually_right_inverse hn

private theorem jet_power_succ {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0) (k n : ℕ) :
    iteratedDeriv n (fun p => Q p ^ (k + 1)) 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i (fun p => Q p ^ k) 0 * iteratedDeriv (n - i) Q 0 := by
  simp only [pow_succ]
  exact iteratedDeriv_fun_mul (hQ.fun_pow k).contDiffAt hQ.contDiffAt

private theorem jet_power_two {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : deriv Q 0 = 1) :
    iteratedDeriv 3 (fun p => Q p ^ 2) 0 = 6 * iteratedDeriv 2 Q 0 ∧
    iteratedDeriv 4 (fun p => Q p ^ 2) 0 =
      8 * iteratedDeriv 3 Q 0 + 6 * iteratedDeriv 2 Q 0 ^ 2 := by
  constructor <;> rw [jet_power_succ hQ 1] <;>
    norm_num [Nat.choose, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0, h1] <;> ring

private theorem jet_power_three {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : deriv Q 0 = 1) :
    iteratedDeriv 3 (fun p => Q p ^ 3) 0 = 6 ∧
    iteratedDeriv 4 (fun p => Q p ^ 3) 0 = 36 * iteratedDeriv 2 Q 0 := by
  have h20 : iteratedDeriv 0 (fun p => Q p ^ 2) 0 = 0 := by simp [iteratedDeriv_zero, h0]
  have h21 : iteratedDeriv 1 (fun p => Q p ^ 2) 0 = 0 := by
    rw [jet_power_succ hQ 1]
    simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0]
  have h22 : iteratedDeriv 2 (fun p => Q p ^ 2) 0 = 2 := by
    rw [jet_power_succ hQ 1]
    norm_num [Nat.choose, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0, h1]
  constructor <;> rw [jet_power_succ hQ 2] <;>
    norm_num [Nat.choose, Finset.sum_range_succ, h20, h21, h22, (jet_power_two hQ h0 h1).1,
      iteratedDeriv_zero, iteratedDeriv_one, h0, h1]
  ring

private theorem jet_power_four {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : deriv Q 0 = 1) :
    iteratedDeriv 3 (fun p => Q p ^ 4) 0 = 0 ∧
    iteratedDeriv 4 (fun p => Q p ^ 4) 0 = 24 := by
  have h30 : iteratedDeriv 0 (fun p => Q p ^ 3) 0 = 0 := by simp [iteratedDeriv_zero, h0]
  have h31 : iteratedDeriv 1 (fun p => Q p ^ 3) 0 = 0 := by
    rw [jet_power_succ hQ 2]
    simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0]
  have h32 : iteratedDeriv 2 (fun p => Q p ^ 3) 0 = 0 := by
    rw [jet_power_succ hQ 2]
    norm_num [Nat.choose, Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0]
    have hd := (hQ.differentiableAt.hasDerivAt.fun_pow 2).deriv
    exact Or.inl (by simpa [h0] using hd)
  constructor <;> rw [jet_power_succ hQ 3] <;>
    norm_num [Nat.choose, Finset.sum_range_succ, h30, h31, h32, (jet_power_three hQ h0 h1).1,
      iteratedDeriv_zero, iteratedDeriv_one, h0, h1]

private theorem jet_high_zero {n k : ℕ} (hk : n < k) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) : iteratedDeriv n (fun z => z ^ k * f z) 0 = 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≠ k := by have := Finset.mem_range.mp hi; omega
  simp only [iteratedDeriv_fun_pow_zero, hik, ite_false, Nat.cast_zero, mul_zero, zero_mul]

/-- The first nontrivial coefficients of any normalized analytic square-root inverse. -/
theorem puiseux_inverse_derivatives {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) :
    iteratedDeriv 2 Q 0 = -(2 / 3 : ℂ) ∧ iteratedDeriv 3 Q 0 = (11 / 12 : ℂ) := by
  obtain ⟨R, hR, hforward⟩ := exists_branchSeries_quartic_remainder
  obtain ⟨S, hS, hfactor⟩ := hQ.exists_eq_sum_add_pow_mul 1
  have hfac (p : ℂ) : Q p = p * S p := by simpa [iteratedDeriv_zero, h0] using hfactor p
  let T : ℂ → ℂ := fun p => S p ^ 5 * R (Q p)
  have hT : AnalyticAt ℂ T 0 :=
    (hS.fun_pow 5).fun_mul ((show AnalyticAt ℂ R (Q 0) by simpa [h0] using hR).fun_comp hQ)
  have heq : ∀ᶠ p in 𝓝 0, p ^ 2 = Q p ^ 2 + (2 / 3 : ℂ) * Q p ^ 3 +
      (1 / 4 : ℂ) * Q p ^ 4 + p ^ 5 * T p := by
    filter_upwards [he] with p hp
    rw [← hp, hforward]
    congr 1
    dsimp [T]
    rw [hfac p, mul_pow]
    ring
  have hj (n : ℕ) (hn : n < 5) : iteratedDeriv n (fun p : ℂ => p ^ 2) 0 =
      iteratedDeriv n (fun p => Q p ^ 2) 0 +
        (2 / 3 : ℂ) * iteratedDeriv n (fun p => Q p ^ 3) 0 +
        (1 / 4 : ℂ) * iteratedDeriv n (fun p => Q p ^ 4) 0 := by
    have h := Filter.EventuallyEq.iteratedDeriv_eq n heq
    have hQc : ContDiffAt ℂ n Q 0 := hQ.contDiffAt
    have hrem : ContDiffAt ℂ n (fun p : ℂ => p ^ 5 * T p) 0 :=
      ((analyticAt_id.fun_pow 5).fun_mul hT).contDiffAt
    rw [iteratedDeriv_fun_add (f := fun p => Q p ^ 2 + (2 / 3 : ℂ) * Q p ^ 3 + (1 / 4 : ℂ) * Q p ^ 4)
      (g := fun p => p ^ 5 * T p) (by fun_prop) hrem, jet_high_zero hn hT, add_zero] at h
    simpa (disch := fun_prop) only [iteratedDeriv_fun_add,
      iteratedDeriv_const_mul_field] using h
  have h3 := hj 3 (by decide)
  rw [(jet_power_two hQ h0 h1.deriv).1, (jet_power_three hQ h0 h1.deriv).1,
    (jet_power_four hQ h0 h1.deriv).1] at h3
  norm_num [iteratedDeriv_fun_pow_zero] at h3
  have h2 : iteratedDeriv 2 Q 0 = -(2 / 3 : ℂ) := by linear_combination -(1 / 6 : ℂ) * h3
  refine ⟨h2, ?_⟩
  have h4 := hj 4 (by decide)
  rw [(jet_power_two hQ h0 h1.deriv).2, (jet_power_three hQ h0 h1.deriv).2,
    (jet_power_four hQ h0 h1.deriv).2, h2] at h4
  norm_num [iteratedDeriv_fun_pow_zero] at h4
  linear_combination -(1 / 8 : ℂ) * h4

/-- The analytic inverse in the square-root parameter has the cubic expansion
`Q(p) = p - p²/3 + 11p³/72 + p⁴R(p)`. -/
theorem puiseux_inverse_cubic_remainder {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ p in 𝓝 0,
      Q p = p - p ^ 2 / 3 + (11 / 72 : ℂ) * p ^ 3 + p ^ 4 * R p := by
  obtain ⟨h2, h3⟩ := puiseux_inverse_derivatives hQ h0 h1 he
  obtain ⟨R, hR, h⟩ := hQ.exists_eventuallyEq_sum_add_pow_mul 4
  refine ⟨R, hR, ?_⟩
  filter_upwards [h] with p hp
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    h0, h1.deriv, h2, h3, smul_eq_mul] at hp
  convert hp using 1; ring

/-- A convergent local inverse in the square-root parameter. The coefficients
beyond those computed explicitly are its ordinary Taylor coefficients. -/
theorem exists_convergent_puiseux_inverse :
    ∃ Q R : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
      (∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 ∧
        Q p = p - p ^ 2 / 3 + (11 / 72 : ℂ) * p ^ 3 + p ^ 4 * R p) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ p : ℂ, ‖p‖ < r →
        HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * iteratedDeriv n Q 0 * p ^ n) (Q p) := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, hsq, hleft, hright⟩ := exists_puiseux_coordinates
  have he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 := by
    filter_upwards [hright] with p hp
    rw [← hsq, hp]
  obtain ⟨R, hR, hseries⟩ := puiseux_inverse_cubic_remainder hQ hQ0 hdQ he
  refine ⟨Q, R, hQ, hR, he.and hseries, ?_⟩
  obtain ⟨r, hr, hball⟩ := hQ.exists_ball_analyticOnNhd
  refine ⟨r, hr, fun p hp => ?_⟩
  have hd : DifferentiableOn ℂ Q (Metric.ball 0 r) :=
    fun z hz => (hball z hz).differentiableAt.differentiableWithinAt
  convert Complex.hasSum_taylorSeries_on_ball hd (by simpa using hp) using 1
  funext n
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The expansion for either principal boundary convention. The parameter
`p = P (W(z) + 1)` is the square root normalized by `P(0)=0`, `P'(0)=1`;
its sign is selected by the branch, rather than chosen independently. -/
theorem exists_principal_puiseux_expansion :
    ∃ P R : ℂ → ℂ, AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R 0 ∧
      P 0 = 0 ∧ HasDerivAt P 1 0 ∧
      (∀ side : BoundarySide, ∀ z : ℂ,
        P (principalWithBoundary side z + 1) ^ 2 =
          2 * Complex.exp 1 * (z - ((-Real.exp (-1) : ℝ) : ℂ))) ∧
      (∀ side : BoundarySide, ∀ᶠ z in 𝓝 (((-Real.exp (-1) : ℝ) : ℂ)),
        let p := P (principalWithBoundary side z + 1)
        principalWithBoundary side z = -1 + p - p ^ 2 / 3 +
          (11 / 72 : ℂ) * p ^ 3 + p ^ 4 * R p) := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, hsq, hleft, hright⟩ := exists_puiseux_coordinates
  have he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 := by
    filter_upwards [hright] with p hp
    rw [← hsq, hp]
  obtain ⟨R, hR, hseries⟩ := puiseux_inverse_cubic_remainder hQ hQ0 hdQ he
  refine ⟨P, R, hP, hR, hP0, hdP, ?_, ?_⟩
  · intro side z
    rw [hsq, branchSeries_eq, add_sub_cancel_right, mulExp_principalWithBoundary]
    congr 2
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, mulExp_ofReal, Real.mulExp_neg_one]
  · intro side
    have hw : Tendsto (fun z => principalWithBoundary side z + 1)
        (𝓝 (((-Real.exp (-1) : ℝ) : ℂ))) (𝓝 0) := by
      simpa only [principalWithBoundary_branchPoint, neg_add_cancel] using
        (continuousAt_principalWithBoundary_branchPoint side).tendsto.add_const 1
    have hp : Tendsto (fun z => P (principalWithBoundary side z + 1))
        (𝓝 (((-Real.exp (-1) : ℝ) : ℂ))) (𝓝 0) := by
      simpa only [Function.comp_def, hP0] using hP.continuousAt.tendsto.comp hw
    filter_upwards [hw.eventually hleft, hp.eventually hseries] with z hz hsz
    dsimp only
    rw [hz] at hsz
    linear_combination hsz

end LambertW.Complex
