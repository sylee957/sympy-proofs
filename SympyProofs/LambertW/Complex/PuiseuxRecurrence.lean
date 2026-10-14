import SympyProofs.LambertW.Complex.Puiseux

/-!
# A rational recurrence for every Puiseux coefficient

`puiseuxDerivative` computes the derivatives `d_n = Q^(n)(0)` using rational
arithmetic, starting from `d_0 = 0` and `d_1 = 1`. `puiseuxCoeff n = d_n / n!`
is the coefficient of `p^n` in `Q`, where the Lambert W value is `-1 + Q(p)`.

The recurrence follows from `(p² - 2) Q Q' = 2p(Q - 1)`.
`puiseuxCoeff_eq_taylorCoeff` proves agreement at every index, and
`exists_pos_hasSum_puiseuxCoeff` proves local convergence of this explicit series.

For example, `#eval (List.range 8).map puiseuxCoeff` computes eight coefficients.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- Differential equation for the normalized inverse, with no division at zero. -/
theorem puiseux_inverse_ode {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) :
    ∀ᶠ p in 𝓝 0, (p ^ 2 - 2) * (Q p * deriv Q p) = 2 * p * (Q p - 1) := by
  have he' : (fun p => branchSeries (Q p)) =ᶠ[𝓝 0] (fun p => p ^ 2) := he
  have hd := he'.deriv
  filter_upwards [he, hd, hQ.eventually_analyticAt] with p hp hdp hQa
  have hf : HasDerivAt branchSeries (2 * Complex.exp (Q p) * Q p) (Q p) := by
    have hh := (analyticAt_branchSeries (Q p)).differentiableAt.hasDerivAt
    have hv := congrFun (iteratedDeriv_branchSeries 0) (Q p)
    simp only [Nat.zero_add, iteratedDeriv_one, Nat.cast_zero, add_zero] at hv
    rw [hv] at hh
    exact hh
  have hcomp := (hf.comp p hQa.differentiableAt.hasDerivAt).deriv
  have hpder : 2 * Complex.exp (Q p) * Q p * deriv Q p = 2 * p := by
    simp only [Function.comp_def] at hcomp
    rw [hcomp] at hdp
    simpa using hdp
  dsimp [branchSeries] at hp
  linear_combination -(Q p * deriv Q p) * hp + (Q p - 1) * hpder

private theorem jet_id_mul (n : ℕ) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    iteratedDeriv (n + 1) (fun z => z * f z) 0 =
      (n + 1 : ℂ) * iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

/-- Recurrence for the unnormalized derivatives `d_n = Q^(n)(0)`.
The Taylor coefficient is `d_n / n!`. -/
theorem puiseux_derivative_recurrence {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) (k : ℕ) :
    iteratedDeriv (k + 2) Q 0 =
      (((k + 2 : ℂ) * (k + 1) *
          ∑ i : Fin (k + 1), (k.choose i : ℂ) * iteratedDeriv i Q 0 * iteratedDeriv (k + 1 - i) Q 0) -
        2 * (k + 2) * iteratedDeriv (k + 1) Q 0 -
        2 * ∑ i : Fin k, ((k + 2).choose (i + 2) : ℂ) *
          iteratedDeriv (i + 2) Q 0 * iteratedDeriv (k + 1 - i) Q 0) / (2 * (k + 3)) := by
  let A : ℂ → ℂ := fun p => Q p * deriv Q p
  have hA : AnalyticAt ℂ A 0 := hQ.fun_mul hQ.deriv
  have hode : (fun p => p * (p * A p) - 2 * A p) =ᶠ[𝓝 0]
      (fun p => 2 * (p * Q p) - 2 * p) := by
    filter_upwards [puiseux_inverse_ode hQ he] with p hp
    dsimp [A]
    linear_combination hp
  have hd := hode.iteratedDeriv_eq (k + 2)
  have hQc : ContDiffAt ℂ (k + 2) Q 0 := hQ.contDiffAt
  have hAc : ContDiffAt ℂ (k + 2) A 0 := hA.contDiffAt
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)] at hd
  simp only [iteratedDeriv_const_mul_field] at hd
  rw [jet_id_mul (k + 1) (f := fun p => p * A p) (analyticAt_id.fun_mul hA), jet_id_mul k hA,
    jet_id_mul (k + 1) hQ] at hd
  have hid : iteratedDeriv (k + 2) (fun p : ℂ => p) 0 = 0 := by
    rw [iteratedDeriv_fun_id_zero]; simp
  have hlin : iteratedDeriv (k + 2) (fun p : ℂ => 2 * p) 0 = 0 := by
    have hh := iteratedDeriv_const_mul_field (n := k + 2) (x := (0 : ℂ)) (2 : ℂ) (fun p : ℂ => p)
    simpa [iteratedDeriv_fun_id_zero] using hh
  rw [hlin, sub_zero] at hd
  have hprod (n : ℕ) : iteratedDeriv n A 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i Q 0 * iteratedDeriv (n + 1 - i) Q 0 := by
    rw [iteratedDeriv_fun_mul hQ.contDiffAt hQ.deriv.contDiffAt]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← iteratedDeriv_succ']
    congr 2
    omega
  rw [hprod k, hprod (k + 2)] at hd
  let B : ℕ → ℂ := fun i => ((k + 2).choose i : ℂ) * iteratedDeriv i Q 0 *
    iteratedDeriv (k + 3 - i) Q 0
  have hsplit : (∑ i ∈ Finset.range (k + 2), B i) =
      B 0 + B 1 + ∑ i ∈ Finset.range k, B (i + 2) := by
    calc
      _ = ∑ i ∈ Finset.range (2 + k), B i := by rw [Nat.add_comm k 2]
      _ = _ := by rw [Finset.sum_range_add]; simp [Finset.sum_range_succ, Nat.add_comm]
  have hfull : (∑ i ∈ Finset.range (k + 3), B i) =
      (k + 3 : ℂ) * iteratedDeriv (k + 2) Q 0 + ∑ i ∈ Finset.range k, B (i + 2) := by
    rw [Finset.sum_range_succ, hsplit]
    simp [B, iteratedDeriv_zero, iteratedDeriv_one, h0, h1.deriv]
    ; ring
  change _ - 2 * (∑ i ∈ Finset.range (k + 3), B i) = _ at hd
  rw [hfull] at hd
  have hb (i : ℕ) : B (i + 2) = ((k + 2).choose (i + 2) : ℂ) *
      iteratedDeriv (i + 2) Q 0 * iteratedDeriv (k + 1 - i) Q 0 := by
    dsimp [B]
    rw [show k + 3 - (i + 2) = k + 1 - i by omega]
  simp only [hb] at hd
  rw [Fin.sum_univ_eq_sum_range (fun i => (k.choose i : ℂ) *
    iteratedDeriv i Q 0 * iteratedDeriv (k + 1 - i) Q 0) (k + 1),
    Fin.sum_univ_eq_sum_range (fun i => ((k + 2).choose (i + 2) : ℂ) *
    iteratedDeriv (i + 2) Q 0 * iteratedDeriv (k + 1 - i) Q 0) k]
  have hn : (2 : ℂ) * (k + 3) ≠ 0 := by
    have : (k + 3 : ℂ) ≠ 0 := by exact_mod_cast (show k + 3 ≠ 0 by omega)
    exact mul_ne_zero (by norm_num) this
  apply (eq_div_iff hn).mpr
  push_cast at hd
  linear_combination -hd

/-- Exact rational derivatives of the normalized Puiseux inverse.
Every index on the right is smaller than the index being computed. -/
def puiseuxDerivative : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k + 2 =>
      (((k + 2 : ℚ) * (k + 1) *
          ∑ i : Fin (k + 1), (k.choose i : ℚ) * puiseuxDerivative i * puiseuxDerivative (k + 1 - i)) -
        2 * (k + 2) * puiseuxDerivative (k + 1) -
        2 * ∑ i : Fin k, ((k + 2).choose (i + 2) : ℚ) *
          puiseuxDerivative (i + 2) * puiseuxDerivative (k + 1 - i)) / (2 * (k + 3))
termination_by n => n

/-- Computable coefficients of `Q(p) = ∑ a_n p^n`, so `W = -1 + Q`. -/
def puiseuxCoeff (n : ℕ) : ℚ := puiseuxDerivative n / n.factorial

/-- The recurrence computes the actual analytic derivatives, not merely a
formal candidate sequence. -/
theorem puiseuxDerivative_eq_iteratedDeriv {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) (n : ℕ) :
    (puiseuxDerivative n : ℂ) = iteratedDeriv n Q 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · simp [puiseuxDerivative, iteratedDeriv_zero, h0]
    · simp [puiseuxDerivative, iteratedDeriv_one, h1.deriv]
    · rw [puiseuxDerivative, puiseux_derivative_recurrence hQ h0 h1 he k]
      push_cast
      simp (disch := omega) only [ih]

/-- Every rational coefficient returned by the algorithm is the corresponding
Taylor coefficient of the analytic inverse. -/
theorem puiseuxCoeff_eq_taylorCoeff {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) (n : ℕ) :
    (puiseuxCoeff n : ℂ) = (n.factorial : ℂ)⁻¹ * iteratedDeriv n Q 0 := by
  unfold puiseuxCoeff
  push_cast
  rw [puiseuxDerivative_eq_iteratedDeriv hQ h0 h1 he]
  ring

/-- The computable coefficient sequence converges to every normalized local
inverse on some positive-radius disk. -/
theorem exists_pos_hasSum_puiseuxCoeff {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0)
    (h0 : Q 0 = 0) (h1 : HasDerivAt Q 1 0)
    (he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : ℂ, ‖p‖ < r →
      HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * p ^ n) (Q p) := by
  obtain ⟨r, hr, hball⟩ := hQ.exists_ball_analyticOnNhd
  refine ⟨r, hr, fun p hp => ?_⟩
  have hd : DifferentiableOn ℂ Q (Metric.ball 0 r) :=
    fun z hz => (hball z hz).differentiableAt.differentiableWithinAt
  have hs := Complex.hasSum_taylorSeries_on_ball hd (by simpa using hp)
  convert hs using 1
  funext n
  rw [puiseuxCoeff_eq_taylorCoeff hQ h0 h1 he]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- An analytic inverse represented by the explicit rational recurrence exists. -/
theorem exists_puiseux_inverse_with_computable_coefficients :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = 0 ∧ HasDerivAt Q 1 0 ∧
      (∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ p : ℂ, ‖p‖ < r →
        HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * p ^ n) (Q p) := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, hsq, hleft, hright⟩ := exists_puiseux_coordinates
  have he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 := by
    filter_upwards [hright] with p hp
    rw [← hsq, hp]
  exact ⟨Q, hQ, hQ0, hdQ, he, exists_pos_hasSum_puiseuxCoeff hQ hQ0 hdQ he⟩

end LambertW.Complex
