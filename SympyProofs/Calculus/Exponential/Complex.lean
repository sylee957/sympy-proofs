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

/-- The general `n`th derivative of `Complex.exp ∘ f`, assuming `C^n` regularity over `ℂ`. -/
theorem iteratedDeriv_cexp_comp {f : ℂ → ℂ} (n : ℕ) (hf : ContDiff ℂ n f) :
    iteratedDeriv n (Complex.exp ∘ f) =
      (Complex.exp ∘ f) * expDerivFactor f n := by
  induction n with
  | zero =>
    funext z
    simp [expDerivFactor]
  | succ n ih =>
    have hfn : ContDiff ℂ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfd : Differentiable ℂ f := hf.differentiable (by simp)
    have hfactor : expDerivFactor f n = fun z =>
        iteratedDeriv n (Complex.exp ∘ f) z / Complex.exp (f z) := by
      funext z
      rw [ih hfn]
      simp [Complex.exp_ne_zero]
    have hfactor_diff : Differentiable ℂ (expDerivFactor f n) := by
      rw [hfactor]
      exact (hf.cexp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)).div
        hfd.cexp (fun z => Complex.exp_ne_zero (f z))
    rw [iteratedDeriv_succ, ih hfn]
    funext z
    simp only [Function.comp_def]
    rw [deriv_mul (hfd z).cexp (hfactor_diff z), deriv_cexp (hfd z)]
    simp only [Pi.mul_apply, expDerivFactor_succ]
    ring

/-- The complex affine case: `D^n exp (a*z + b) = a^n * exp (a*z + b)`. -/
theorem iteratedDeriv_cexp_affine (n : ℕ) (a b : ℂ) :
    iteratedDeriv n (Complex.exp ∘ fun z => a * z + b) =
      fun z => a ^ n * Complex.exp (a * z + b) := by
  simp_rw [Function.comp_def, Complex.exp_add]
  funext z
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_cexp_const_mul]
  simp [mul_assoc]

theorem iteratedDeriv_two_cexp_comp {f : ℂ → ℂ} (hf : ContDiff ℂ 2 f) (z : ℂ) :
    iteratedDeriv 2 (Complex.exp ∘ f) z =
      Complex.exp (f z) * (deriv f z ^ 2 + iteratedDeriv 2 f z) := by
  simp only [iteratedDeriv_cexp_comp 2 hf, Pi.mul_apply, Function.comp_apply, expDerivFactor_two]

/-- Under complex `C^{n+1}` regularity, the `n`th derivative has the stated derivative. -/
theorem hasDerivAt_iteratedDeriv_cexp_comp {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiff ℂ (n + 1 : ℕ) f) (z : ℂ) :
    HasDerivAt (iteratedDeriv n (Complex.exp ∘ f))
      (((Complex.exp ∘ f) * expDerivFactor f (n + 1)) z) z := by
  have hd : DifferentiableAt ℂ (iteratedDeriv n (Complex.exp ∘ f)) z :=
    hf.cexp.differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n) z
  simpa only [← iteratedDeriv_succ, iteratedDeriv_cexp_comp (n + 1) hf] using hd.hasDerivAt

/-- The cached Bell evaluator computes the complex `n`th derivative factor. -/
theorem iteratedDeriv_cexp_comp_imperative {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiff ℂ n f) :
    iteratedDeriv n (Complex.exp ∘ f) =
      (Complex.exp ∘ f) * expDerivFactorImperative f n := by
  simp only [expDerivFactorImperative_eq_bell]
  cases n with
  | zero =>
    funext z
    simp
  | succ n =>
    funext z
    apply iteratedDeriv_eq_mul_expBellFactor (n + 1) hf.contDiffAt hf.cexp.contDiffAt
    exact Filter.Eventually.of_forall (fun w => by
      simpa only [mul_comm] using deriv_cexp (hf.differentiable (by simp) w))

/-- Under complex `C^n` regularity the cached and differential recurrences agree. -/
theorem expDerivFactorImperative_eq_complex {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiff ℂ n f) : expDerivFactorImperative f n = expDerivFactor f n := by
  funext z
  apply mul_left_cancel₀ (Complex.exp_ne_zero (f z))
  exact (congrFun (iteratedDeriv_cexp_comp_imperative n hf) z).symm.trans
    (congrFun (iteratedDeriv_cexp_comp n hf) z)

/-- The complex derivative witness expressed using the cached evaluator. -/
theorem hasDerivAt_iteratedDeriv_cexp_comp_imperative {f : ℂ → ℂ} (n : ℕ)
    (hf : ContDiff ℂ (n + 1 : ℕ) f) (z : ℂ) :
    HasDerivAt (iteratedDeriv n (Complex.exp ∘ f))
      (((Complex.exp ∘ f) * expDerivFactorImperative f (n + 1)) z) z := by
  simpa only [expDerivFactorImperative_eq_complex (n + 1) hf] using
    hasDerivAt_iteratedDeriv_cexp_comp n hf z

end SympyProofs.Calculus.Exponential
