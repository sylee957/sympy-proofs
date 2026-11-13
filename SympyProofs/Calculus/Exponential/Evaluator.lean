module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Tactic.Ring

/-!
# Recurrence evaluator for exponential derivatives

`expDerivFactor f n` is the factor `Pₙ` defined by `P₀ = 1` and
`Pₙ₊₁ = Pₙ' + f' * Pₙ`. The definition and its first values are shared
by the real and complex derivative formulas.

`expBellFactor` gives the algebraic Bell recurrence in the derivatives of `f`.
`expDerivFactorImperative` computes it with separate mutable arrays `derivatives`
and `factors`, both growing via `push`. It never differentiates a previously
computed factor. Each array maintains its own positive length, with proof-checked
indexing.
The inner loop updates one binomial coefficient by exact natural-number
division while accumulating the next factor, outside its function of `x`.

`expDerivFactorImperative_eq_bell` verifies the cache implementation without
regularity assumptions. The real, complex, and analytic modules connect it to
the differential recurrence under the corresponding regularity assumptions.
-/

@[expose] public section

namespace SympyProofs.Calculus.Exponential

open scoped BigOperators Topology

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

/-- The Bell recurrence `Pₙ₊₁ = ∑ k ≤ n, choose n k * f⁽ᵏ⁺¹⁾ * Pₙ₋ₖ`. -/
noncomputable def expBellFactor (f : 𝕜 → 𝕜) (n : ℕ) : 𝕜 → 𝕜 :=
  match n with
  | 0 => fun _ => 1
  | n + 1 => fun x => ∑ k : Fin (n + 1),
      (n.choose k : 𝕜) * iteratedDeriv (k + 1) f x * expBellFactor f (n - k) x
termination_by n

@[simp] theorem expBellFactor_zero (f : 𝕜 → 𝕜) : expBellFactor f 0 = fun _ => 1 := by
  rw [expBellFactor]

theorem expBellFactor_succ (f : 𝕜 → 𝕜) (n : ℕ) (x : 𝕜) :
    expBellFactor f (n + 1) x = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : 𝕜) * iteratedDeriv (k + 1) f x * expBellFactor f (n - k) x := by
  rw [expBellFactor]
  exact Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : 𝕜) * iteratedDeriv (k + 1) f x * expBellFactor f (n - k) x)
    (n + 1)

/-- Compute the final Bell factor using separate mutable derivative and factor caches.

The arrays start empty and are seeded with `f` and `P₀ = 1`. Each outer iteration
pushes the next derivative and Bell factor into their respective arrays.
Each cache carries its own nonempty proof, which supplies the bounds proofs.
The last Bell summand is the new derivative itself; the inner loop adds the
remaining summands, updating the binomial coefficient inline by exact division
in `ℕ`, then casting it into the target field.
This remains noncomputable because it uses `deriv`. -/
noncomputable def expDerivFactorImperative (f : 𝕜 → 𝕜) (n : ℕ) : 𝕜 → 𝕜 := Id.run do
  let mut derivatives : { a : Array (𝕜 → 𝕜) // 0 < a.size } :=
    ⟨#[].push f, by simp⟩
  let mut factors : { a : Array (𝕜 → 𝕜) // 0 < a.size } :=
    ⟨#[].push (fun _ => 1), by simp⟩
  for _ in List.range n do
    have hderivatives := derivatives.property
    have hfactors := factors.property
    let m := factors.val.size - 1
    let nextDerivative := deriv (derivatives.val[derivatives.val.size - 1]'(by omega))
    let mut coefficient : ℕ := 1
    -- The last Bell summand is just the new derivative, since choose m m = P₀ = 1.
    let mut next : 𝕜 → 𝕜 := nextDerivative
    for k in List.finRange (derivatives.val.size - 1) do
      next := fun x => next x + (coefficient : 𝕜) *
        (derivatives.val[k.val + 1]'(by omega)) x * (factors.val[m - k.val]'(by omega)) x
      coefficient := coefficient * (m - k.val) / (k.val + 1)
    derivatives := ⟨derivatives.val.push nextDerivative, by simp⟩
    factors := ⟨factors.val.push next, by simp⟩
  return factors.val[factors.val.size - 1]'(by have := factors.property; omega)

/-- The inner loop accumulates the remaining Bell summands and advances the coefficient. -/
private theorem bell_sum_fold
    (ds ps : { a : Array (𝕜 → 𝕜) // 0 < a.size })
    (t : ℕ) (ht : t ≤ ds.val.size - 1) :
    let df := deriv (ds.val[ds.val.size - 1]'(by have := ds.property; omega))
    (List.finRange t).foldl
      (fun (state : ℕ × (𝕜 → 𝕜)) k =>
        (state.1 * (ps.val.size - 1 - k.val) / (k.val + 1),
          fun x => state.2 x + (state.1 : 𝕜) *
            (ds.val[k.val + 1]'(by have := ds.property; omega)) x *
            (ps.val[ps.val.size - 1 - k.val]'(by have := ps.property; omega)) x)) (1, df) =
      ((ps.val.size - 1).choose t, fun x => df x + ∑ k : Fin t,
        ((ps.val.size - 1).choose k.val : 𝕜) *
          (ds.val[k.val + 1]'(by have := ds.property; omega)) x *
          (ps.val[ps.val.size - 1 - k.val]'(by have := ps.property; omega)) x) := by
  dsimp only
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.finRange_succ_last]
    simp only [List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil,
      Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega)]
    rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos t)]
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, add_assoc]

/-- After `n` iterations, both caches contain exactly the entries of orders `0` through `n`. -/
private theorem caches_fold (f : 𝕜 → 𝕜) (n : ℕ) :
    (List.range n).foldl
      (fun (c : { a : Array (𝕜 → 𝕜) // 0 < a.size } ×
          { a : Array (𝕜 → 𝕜) // 0 < a.size }) _ =>
        have _hds := c.1.property
        have _hps := c.2.property
        let df := deriv (c.1.val[c.1.val.size - 1]'(by omega))
        (⟨c.1.val.push df, by simp⟩,
          ⟨c.2.val.push (fun x => df x + ∑ k : Fin (c.1.val.size - 1),
            ((c.2.val.size - 1).choose k.val : 𝕜) *
              (c.1.val[k.val + 1]'(by omega)) x *
              (c.2.val[c.2.val.size - 1 - k.val]'(by omega)) x), by simp⟩))
      (⟨#[].push f, by simp⟩, ⟨#[].push (fun _ => 1), by simp⟩) =
    (⟨Array.ofFn (fun k : Fin (n + 1) => iteratedDeriv k f), by simp⟩,
      ⟨Array.ofFn (fun k : Fin (n + 1) => expBellFactor f k), by simp⟩) := by
  induction n with
  | zero => simp [Array.ofFn_succ]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      simp only [Array.size_ofFn, Nat.add_sub_cancel, Array.getElem_ofFn]
      conv_rhs => rw [Array.ofFn_succ]
      simp [iteratedDeriv_succ]
    · apply Subtype.ext
      dsimp only
      simp only [Array.size_ofFn, Nat.add_sub_cancel, Array.getElem_ofFn]
      conv_rhs => rw [Array.ofFn_succ]
      congr 1
      funext x
      rw [expBellFactor]
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, expBellFactor_zero, mul_one]
      rw [add_comm]
      congr 1
      · rw [← Fin.sum_congr' _
          (show (Array.ofFn (fun k : Fin (n + 1) => iteratedDeriv k f)).size - 1 = n by simp).symm]
        apply Finset.sum_congr rfl
        intro k hk
        simp
      · rw [iteratedDeriv_succ]

/-- The imperative implementation evaluates the algebraic Bell recurrence exactly. -/
@[simp] theorem expDerivFactorImperative_eq_bell (f : 𝕜 → 𝕜) (n : ℕ) :
    expDerivFactorImperative f n = expBellFactor f n := by
  simp only [expDerivFactorImperative, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind,
    bell_sum_fold _ _ _ (Nat.le_refl _)]
  simp only [caches_fold, Array.size_ofFn, Nat.add_sub_cancel, Array.getElem_ofFn]
  rfl

/-- The Bell formula for a local solution of `g' = f' * g`, by the Leibniz rule. -/
theorem iteratedDeriv_eq_mul_expBellFactor {f g : 𝕜 → 𝕜} {x : 𝕜} (n : ℕ)
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hode : deriv g =ᶠ[𝓝 x] fun x => deriv f x * g x) :
    iteratedDeriv n g x = g x * expBellFactor f n x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hfd : ContDiffAt 𝕜 n (deriv f) x := hf.derivWithin (by simp)
      have hgn : ContDiffAt 𝕜 n g x := hg.of_le (by exact_mod_cast Nat.le_succ n)
      rw [iteratedDeriv_succ', hode.iteratedDeriv_eq n]
      rw [iteratedDeriv_fun_mul hfd hgn, expBellFactor_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← iteratedDeriv_succ']
      have hkn : n - k < n + 1 := by omega
      rw [ih (n - k) hkn
        (hf.of_le (by exact_mod_cast Nat.le_of_lt hkn))
        (hg.of_le (by exact_mod_cast Nat.le_of_lt hkn))]
      ring

end SympyProofs.Calculus.Exponential
