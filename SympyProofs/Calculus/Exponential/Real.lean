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

/-- The general `n`th derivative of `Real.exp ∘ f`, assuming `C^n` regularity over `ℝ`. -/
theorem iteratedDeriv_exp_comp {f : ℝ → ℝ} (n : ℕ) (hf : ContDiff ℝ n f) :
    iteratedDeriv n (Real.exp ∘ f) =
      (Real.exp ∘ f) * expDerivFactor f n := by
  induction n with
  | zero =>
    funext x
    simp [expDerivFactor]
  | succ n ih =>
    have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hfactor : expDerivFactor f n = fun x =>
        iteratedDeriv n (Real.exp ∘ f) x / Real.exp (f x) := by
      funext x
      rw [ih hfn]
      simp [Real.exp_ne_zero]
    have hfactor_diff : Differentiable ℝ (expDerivFactor f n) := by
      rw [hfactor]
      exact (hf.exp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)).div
        hfd.exp (fun x => Real.exp_ne_zero (f x))
    rw [iteratedDeriv_succ, ih hfn]
    funext x
    simp only [Function.comp_def]
    rw [deriv_mul (hfd x).exp (hfactor_diff x), deriv_exp (hfd x)]
    simp only [Pi.mul_apply, expDerivFactor_succ]
    ring

/-- Every derivative of the real exponential is itself. -/
theorem iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- The affine case: `D^n exp (a*x + b) = a^n * exp (a*x + b)`. -/
theorem iteratedDeriv_exp_affine (n : ℕ) (a b : ℝ) :
    iteratedDeriv n (Real.exp ∘ fun x => a * x + b) =
      fun x => a ^ n * Real.exp (a * x + b) := by
  simp_rw [Function.comp_def, Real.exp_add]
  funext x
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_exp_const_mul]
  simp [mul_assoc]

theorem iteratedDeriv_two_exp_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (Real.exp ∘ f) x =
      Real.exp (f x) * (deriv f x ^ 2 + iteratedDeriv 2 f x) := by
  simp only [iteratedDeriv_exp_comp 2 hf, Pi.mul_apply, Function.comp_apply, expDerivFactor_two]

/-- Under `C^{n+1}` regularity, the real `n`th derivative has the stated derivative. -/
theorem hasDerivAt_iteratedDeriv_exp_comp {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (Real.exp ∘ f))
      (((Real.exp ∘ f) * expDerivFactor f (n + 1)) x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv n (Real.exp ∘ f)) x :=
    hf.exp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n) x
  simpa only [← iteratedDeriv_succ, iteratedDeriv_exp_comp (n + 1) hf] using hd.hasDerivAt

/-- The cached Bell evaluator computes the real `n`th derivative factor. -/
theorem iteratedDeriv_exp_comp_imperative {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ n f) :
    iteratedDeriv n (Real.exp ∘ f) =
      (Real.exp ∘ f) * expDerivFactorImperative f n := by
  simp only [expDerivFactorImperative_eq_bell]
  cases n with
  | zero =>
    funext x
    simp
  | succ n =>
    funext x
    apply iteratedDeriv_eq_mul_expBellFactor (n + 1) hf.contDiffAt hf.exp.contDiffAt
    exact Filter.Eventually.of_forall (fun y => by
      simpa only [mul_comm] using deriv_exp (hf.differentiable (by simp) y))

/-- Under real `C^n` regularity the cached and differential recurrences agree. -/
theorem expDerivFactorImperative_eq_real {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ n f) : expDerivFactorImperative f n = expDerivFactor f n := by
  funext x
  apply mul_left_cancel₀ (Real.exp_ne_zero (f x))
  exact (congrFun (iteratedDeriv_exp_comp_imperative n hf) x).symm.trans
    (congrFun (iteratedDeriv_exp_comp n hf) x)

/-- The real derivative witness expressed using the cached evaluator. -/
theorem hasDerivAt_iteratedDeriv_exp_comp_imperative {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (Real.exp ∘ f))
      (((Real.exp ∘ f) * expDerivFactorImperative f (n + 1)) x) x := by
  simpa only [expDerivFactorImperative_eq_real (n + 1) hf] using
    hasDerivAt_iteratedDeriv_exp_comp n hf x

end SympyProofs.Calculus.Exponential
