module

public import SympyProofs.Calculus.Exponential.Evaluator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.Ring

/-!
# Real exponential derivatives

The `n`th derivative formula for `Real.exp ∘ f` under `C^n` regularity,
its basic and affine cases, and `HasDerivAt` witnesses under `C^{n+1}` regularity.
-/

@[expose] public section

namespace SympyProofs.Calculus.Exponential

/-- The general `n`th derivative of `Real.exp (f x)`, assuming `C^n` regularity over `ℝ`. -/
theorem iteratedDeriv_exp_comp {f : ℝ → ℝ} (n : ℕ) (hf : ContDiff ℝ n f) :
    iteratedDeriv n (fun x => Real.exp (f x)) =
      fun x => Real.exp (f x) * expDerivFactor f n x := by
  induction n with
  | zero => simp [expDerivFactor]
  | succ n ih =>
    have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hfactor : expDerivFactor f n = fun x =>
        iteratedDeriv n (fun x => Real.exp (f x)) x / Real.exp (f x) := by
      funext x
      rw [ih hfn]
      simp [Real.exp_ne_zero]
    have hfactor_diff : Differentiable ℝ (expDerivFactor f n) := by
      rw [hfactor]
      exact (hf.exp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)).div
        hfd.exp (fun x => Real.exp_ne_zero (f x))
    rw [iteratedDeriv_succ, ih hfn]
    funext x
    rw [deriv_fun_mul (hfd x).exp (hfactor_diff x), deriv_exp (hfd x)]
    simp only [expDerivFactor_succ]
    ring

/-- Every derivative of the real exponential is itself. -/
theorem iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- The affine case: `D^n exp (a*x + b) = a^n * exp (a*x + b)`. -/
theorem iteratedDeriv_exp_affine (n : ℕ) (a b : ℝ) :
    iteratedDeriv n (fun x => Real.exp (a * x + b)) =
      fun x => a ^ n * Real.exp (a * x + b) := by
  simp_rw [Real.exp_add]
  funext x
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_exp_const_mul]
  simp [mul_assoc]

theorem iteratedDeriv_two_exp_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (fun x => Real.exp (f x)) x =
      Real.exp (f x) * (deriv f x ^ 2 + iteratedDeriv 2 f x) := by
  simp only [iteratedDeriv_exp_comp 2 hf, expDerivFactor_two]

/-- Under `C^{n+1}` regularity, the real `n`th derivative has the stated derivative. -/
theorem hasDerivAt_iteratedDeriv_exp_comp {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (fun x => Real.exp (f x)))
      (Real.exp (f x) * expDerivFactor f (n + 1) x) x := by
  have hd := (hf.exp.differentiable_iteratedDeriv n
    (by exact_mod_cast Nat.lt_succ_self n) x).hasDerivAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_exp_comp (n + 1) hf] using hd

end SympyProofs.Calculus.Exponential
