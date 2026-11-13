module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Tactic.Ring

/-!
# Recurrence evaluator for exponential derivatives

`expDerivFactor f n` is the factor `Pₙ` defined by `P₀ = 1` and
`Pₙ₊₁ = Pₙ' + f' * Pₙ`. The definition and its first values are shared
by the real and complex derivative formulas.

`expDerivFactorImperative` computes the final factor with one mutable function.
Its correctness theorem identifies the result with the recursive specification.
-/

@[expose] public section

namespace SympyProofs.Calculus.Exponential

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The factor multiplying `exp (f x)` in its `n`th derivative, defined by
the differential recurrence for complete exponential Bell polynomials. -/
noncomputable def expDerivFactor (f : 𝕜 → 𝕜) : ℕ → 𝕜 → 𝕜
  | 0 => fun _ => 1
  | n + 1 => fun x => deriv (expDerivFactor f n) x + deriv f x * expDerivFactor f n x

@[simp] theorem expDerivFactor_zero (f : 𝕜 → 𝕜) (x : 𝕜) :
    expDerivFactor f 0 x = 1 := rfl

theorem expDerivFactor_succ (f : 𝕜 → 𝕜) (n : ℕ) (x : 𝕜) :
    expDerivFactor f (n + 1) x =
      deriv (expDerivFactor f n) x + deriv f x * expDerivFactor f n x := rfl

@[simp] theorem expDerivFactor_one (f : 𝕜 → 𝕜) :
    expDerivFactor f 1 = deriv f := by
  funext x
  simp [expDerivFactor]

theorem expDerivFactor_two (f : 𝕜 → 𝕜) (x : 𝕜) :
    expDerivFactor f 2 x = deriv f x ^ 2 + iteratedDeriv 2 f x := by
  rw [expDerivFactor_succ, expDerivFactor_one, iteratedDeriv_succ, iteratedDeriv_one]
  ring

/-- Compute the final factor using one mutable function. -/
noncomputable def expDerivFactorImperative (f : 𝕜 → 𝕜) (n : ℕ) : 𝕜 → 𝕜 := Id.run do
  let df := deriv f
  let mut current : 𝕜 → 𝕜 := fun _ => 1
  for _ in List.range n do
    current := fun x => deriv current x + df x * current x
  return current

@[simp] theorem expDerivFactorImperative_eq (f : 𝕜 → 𝕜) (n : ℕ) :
    expDerivFactorImperative f n = expDerivFactor f n := by
  simp only [expDerivFactorImperative, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  change (List.range n).foldl
    (fun current _ => fun x => deriv current x + deriv f x * current x)
    (fun _ => 1) = expDerivFactor f n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

end SympyProofs.Calculus.Exponential
