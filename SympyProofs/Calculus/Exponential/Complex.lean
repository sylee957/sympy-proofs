module

public import SympyProofs.Calculus.Exponential.Evaluator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.Ring

/-!
# Complex exponential derivatives

The `n`th derivative formula for `Complex.exp ∘ f` under complex `C^n`
regularity, its basic and affine cases, and `HasDerivAt` witnesses.
-/

@[expose] public section

namespace SympyProofs.Calculus.Exponential

/-- Every complex derivative of the complex exponential is itself. -/
theorem iteratedDeriv_cexp (n : ℕ) : iteratedDeriv n Complex.exp = Complex.exp := by
  rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

/-- The general `n`th derivative of `Complex.exp (f z)`, assuming `C^n` regularity over `ℂ`. -/
theorem iteratedDeriv_cexp_comp {f : ℂ → ℂ} (n : ℕ) (hf : ContDiff ℂ n f) :
    iteratedDeriv n (fun z => Complex.exp (f z)) =
      fun z => Complex.exp (f z) * expDerivFactor f n z := by
  induction n with
  | zero => simp [expDerivFactor]
  | succ n ih =>
    have hfn : ContDiff ℂ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfd : Differentiable ℂ f := hf.differentiable (by simp)
    have hfactor : expDerivFactor f n = fun z =>
        iteratedDeriv n (fun z => Complex.exp (f z)) z / Complex.exp (f z) := by
      funext z
      rw [ih hfn]
      simp [Complex.exp_ne_zero]
    have hfactor_diff : Differentiable ℂ (expDerivFactor f n) := by
      rw [hfactor]
      exact (hf.cexp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)).div
        hfd.cexp (fun z => Complex.exp_ne_zero (f z))
    rw [iteratedDeriv_succ, ih hfn]
    funext z
    rw [deriv_fun_mul (hfd z).cexp (hfactor_diff z), deriv_cexp (hfd z)]
    simp only [expDerivFactor_succ]
    ring

/-- The complex affine case: `D^n exp (a*z + b) = a^n * exp (a*z + b)`. -/
theorem iteratedDeriv_cexp_affine (n : ℕ) (a b : ℂ) :
    iteratedDeriv n (fun z => Complex.exp (a * z + b)) =
      fun z => a ^ n * Complex.exp (a * z + b) := by
  simp_rw [Complex.exp_add]
  funext z
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_cexp_const_mul]
  simp [mul_assoc]

theorem iteratedDeriv_two_cexp_comp {f : ℂ → ℂ} (hf : ContDiff ℂ 2 f) (z : ℂ) :
    iteratedDeriv 2 (fun z => Complex.exp (f z)) z =
      Complex.exp (f z) * (deriv f z ^ 2 + iteratedDeriv 2 f z) := by
  simp only [iteratedDeriv_cexp_comp 2 hf, expDerivFactor_two]

/-- Under complex `C^{n+1}` regularity, the `n`th derivative has the stated derivative. -/
theorem hasDerivAt_iteratedDeriv_cexp_comp {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiff ℂ (n + 1 : ℕ) f) (z : ℂ) :
    HasDerivAt (iteratedDeriv n (fun z => Complex.exp (f z)))
      (Complex.exp (f z) * expDerivFactor f (n + 1) z) z := by
  have hd := (hf.cexp.differentiable_iteratedDeriv n
    (by exact_mod_cast Nat.lt_succ_self n) z).hasDerivAt
  simpa only [← iteratedDeriv_succ, iteratedDeriv_cexp_comp (n + 1) hf] using hd

end SympyProofs.Calculus.Exponential
