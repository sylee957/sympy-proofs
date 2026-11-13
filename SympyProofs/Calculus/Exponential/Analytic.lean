module

public import SympyProofs.Calculus.Exponential.Evaluator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

import Mathlib.Tactic.Ring

/-!
# Analyticity and local exponential derivative formulas

The recurrence factors are analytic wherever `f` is analytic. Local
`AnalyticAt` hypotheses give the real and complex `n`th derivative formulas
and `HasDerivAt` witnesses at the evaluation point.
-/

@[expose] public section

namespace SympyProofs.Calculus.Exponential

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The recurrence factors are analytic wherever `f` is analytic. -/
theorem analyticAt_expDerivFactor [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (n : ℕ) : AnalyticAt 𝕜 (expDerivFactor f n) x := by
  induction n with
  | zero => exact analyticAt_const
  | succ n ih => exact ih.deriv.add (hf.deriv.mul ih)

/-- Local real analyticity suffices for the `n`th derivative formula at a point. -/
theorem iteratedDeriv_exp_comp_of_analyticAt {f : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    iteratedDeriv n (Real.exp ∘ f) x =
      ((Real.exp ∘ f) * expDerivFactor f n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (Real.exp ∘ f) =ᶠ[𝓝 x]
        ((Real.exp ∘ f) * expDerivFactor f n) :=
      hf.eventually_analyticAt.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ, heq.deriv_eq]
    simp only [Function.comp_def]
    rw [deriv_mul hf.differentiableAt.exp (analyticAt_expDerivFactor hf n).differentiableAt,
      deriv_exp hf.differentiableAt]
    simp only [Pi.mul_apply, expDerivFactor_succ]
    ring

/-- Local complex analyticity suffices for the `n`th derivative formula at a point. -/
theorem iteratedDeriv_cexp_comp_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    iteratedDeriv n (Complex.exp ∘ f) z =
      ((Complex.exp ∘ f) * expDerivFactor f n) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (Complex.exp ∘ f) =ᶠ[𝓝 z]
        ((Complex.exp ∘ f) * expDerivFactor f n) :=
      hf.eventually_analyticAt.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ, heq.deriv_eq]
    simp only [Function.comp_def]
    rw [deriv_mul hf.differentiableAt.cexp (analyticAt_expDerivFactor hf n).differentiableAt,
      deriv_cexp hf.differentiableAt]
    simp only [Pi.mul_apply, expDerivFactor_succ]
    ring

/-- Local real analyticity gives derivative witnesses for all iterated derivatives. -/
theorem hasDerivAt_iteratedDeriv_exp_comp_of_analyticAt {f : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    HasDerivAt (iteratedDeriv n (Real.exp ∘ f))
      (((Real.exp ∘ f) * expDerivFactor f (n + 1)) x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv n (Real.exp ∘ f)) x := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.rexp.iterated_deriv n).differentiableAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_exp_comp_of_analyticAt (n + 1) hf]
    using hd.hasDerivAt

/-- Local complex analyticity gives derivative witnesses for all iterated derivatives. -/
theorem hasDerivAt_iteratedDeriv_cexp_comp_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (iteratedDeriv n (Complex.exp ∘ f))
      (((Complex.exp ∘ f) * expDerivFactor f (n + 1)) z) z := by
  have hd : DifferentiableAt ℂ (iteratedDeriv n (Complex.exp ∘ f)) z := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.cexp.iterated_deriv n).differentiableAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_cexp_comp_of_analyticAt (n + 1) hf]
    using hd.hasDerivAt

/-- Local real analyticity suffices for the cached Bell derivative formula. -/
theorem iteratedDeriv_exp_comp_imperative_of_analyticAt {f : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    iteratedDeriv n (Real.exp ∘ f) x =
      ((Real.exp ∘ f) * expDerivFactorImperative f n) x := by
  rw [expDerivFactorImperative_eq_bell]
  apply iteratedDeriv_eq_mul_expBellFactor n hf.contDiffAt hf.rexp.contDiffAt
  exact hf.eventually_analyticAt.mono (fun y hy => by
    simpa only [Function.comp_def, mul_comm] using deriv_exp hy.differentiableAt)

/-- Local complex analyticity suffices for the cached Bell derivative formula. -/
theorem iteratedDeriv_cexp_comp_imperative_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    iteratedDeriv n (Complex.exp ∘ f) z =
      ((Complex.exp ∘ f) * expDerivFactorImperative f n) z := by
  rw [expDerivFactorImperative_eq_bell]
  apply iteratedDeriv_eq_mul_expBellFactor n hf.contDiffAt hf.cexp.contDiffAt
  exact hf.eventually_analyticAt.mono (fun w hw => by
    simpa only [Function.comp_def, mul_comm] using deriv_cexp hw.differentiableAt)

theorem expDerivFactorImperative_eq_real_of_analyticAt {f : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hf : AnalyticAt ℝ f x) : expDerivFactorImperative f n x = expDerivFactor f n x := by
  apply mul_left_cancel₀ (Real.exp_ne_zero (f x))
  exact (iteratedDeriv_exp_comp_imperative_of_analyticAt n hf).symm.trans
    (iteratedDeriv_exp_comp_of_analyticAt n hf)

theorem expDerivFactorImperative_eq_complex_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) : expDerivFactorImperative f n z = expDerivFactor f n z := by
  apply mul_left_cancel₀ (Complex.exp_ne_zero (f z))
  exact (iteratedDeriv_cexp_comp_imperative_of_analyticAt n hf).symm.trans
    (iteratedDeriv_cexp_comp_of_analyticAt n hf)

theorem hasDerivAt_iteratedDeriv_exp_comp_imperative_of_analyticAt {f : ℝ → ℝ}
    (n : ℕ) {x : ℝ} (hf : AnalyticAt ℝ f x) :
    HasDerivAt (iteratedDeriv n (Real.exp ∘ f))
      (((Real.exp ∘ f) * expDerivFactorImperative f (n + 1)) x) x := by
  simpa only [Pi.mul_apply, expDerivFactorImperative_eq_real_of_analyticAt (n + 1) hf] using
    hasDerivAt_iteratedDeriv_exp_comp_of_analyticAt n hf

theorem hasDerivAt_iteratedDeriv_cexp_comp_imperative_of_analyticAt {f : ℂ → ℂ}
    (n : ℕ) {z : ℂ} (hf : AnalyticAt ℂ f z) :
    HasDerivAt (iteratedDeriv n (Complex.exp ∘ f))
      (((Complex.exp ∘ f) * expDerivFactorImperative f (n + 1)) z) z := by
  simpa only [Pi.mul_apply, expDerivFactorImperative_eq_complex_of_analyticAt (n + 1) hf] using
    hasDerivAt_iteratedDeriv_cexp_comp_of_analyticAt n hf

end SympyProofs.Calculus.Exponential
