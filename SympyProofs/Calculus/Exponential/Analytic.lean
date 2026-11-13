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
    iteratedDeriv n (fun x => Real.exp (f x)) x =
      Real.exp (f x) * expDerivFactor f n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun x => Real.exp (f x)) =ᶠ[𝓝 x]
        (fun x => Real.exp (f x) * expDerivFactor f n x) :=
      hf.eventually_analyticAt.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ, heq.deriv_eq,
      deriv_fun_mul hf.differentiableAt.exp (analyticAt_expDerivFactor hf n).differentiableAt,
      deriv_exp hf.differentiableAt, expDerivFactor_succ]
    ring

/-- Local complex analyticity suffices for the `n`th derivative formula at a point. -/
theorem iteratedDeriv_cexp_comp_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    iteratedDeriv n (fun z => Complex.exp (f z)) z =
      Complex.exp (f z) * expDerivFactor f n z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun z => Complex.exp (f z)) =ᶠ[𝓝 z]
        (fun z => Complex.exp (f z) * expDerivFactor f n z) :=
      hf.eventually_analyticAt.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ, heq.deriv_eq,
      deriv_fun_mul hf.differentiableAt.cexp (analyticAt_expDerivFactor hf n).differentiableAt,
      deriv_cexp hf.differentiableAt, expDerivFactor_succ]
    ring

/-- Local real analyticity gives derivative witnesses for all iterated derivatives. -/
theorem hasDerivAt_iteratedDeriv_exp_comp_of_analyticAt {f : ℝ → ℝ} (n : ℕ) {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    HasDerivAt (iteratedDeriv n (fun x => Real.exp (f x)))
      (Real.exp (f x) * expDerivFactor f (n + 1) x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv n (fun x => Real.exp (f x))) x := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.rexp.iterated_deriv n).differentiableAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_exp_comp_of_analyticAt (n + 1) hf]
    using hd.hasDerivAt

/-- Local complex analyticity gives derivative witnesses for all iterated derivatives. -/
theorem hasDerivAt_iteratedDeriv_cexp_comp_of_analyticAt {f : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    HasDerivAt (iteratedDeriv n (fun z => Complex.exp (f z)))
      (Complex.exp (f z) * expDerivFactor f (n + 1) z) z := by
  have hd : DifferentiableAt ℂ (iteratedDeriv n (fun z => Complex.exp (f z))) z := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.cexp.iterated_deriv n).differentiableAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_cexp_comp_of_analyticAt (n + 1) hf]
    using hd.hasDerivAt

end SympyProofs.Calculus.Exponential
