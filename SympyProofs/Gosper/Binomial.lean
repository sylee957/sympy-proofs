module

public import SympyProofs.Gosper.Basic

/-! # Binomial identities and parameter conditions

The binomial-quotient identity on p. 41 and the alternating binomial sum.
The latter records the exceptional parameter in SymPy issue #30593:
https://github.com/sympy/sympy/issues/30593.
-/

@[expose] public section
noncomputable section

namespace Gosper

variable {K : Type*} [Field K] [CharZero K]

private theorem choose_upper_step (x : K) (n : ℕ) :
    (x + 1 - n) * Ring.choose (x + 1) n = (x + 1) * Ring.choose x n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Ring.choose_smul_choose x (n := n + 1) (k := n) (by omega)
    simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
      nsmul_eq_mul] at h
    rw [Ring.choose_succ_succ]
    push_cast at h ⊢
    linear_combination -h

def binomialBoundary (p r : K) (q : ℕ) (x : K) : K :=
  (x + r - q - 1) * (x + p - q + 1) * Ring.choose (x + p + 1) q /
    (((q : K) + 1) * (p - r + 1) * Ring.choose (x + r) (q + 2))

theorem binomial_boundary_step (p r : K) (q : ℕ) (x : K)
    (hpr : p - r + 1 ≠ 0)
    (h0 : Ring.choose (x + r) (q + 2) ≠ 0)
    (h1 : Ring.choose (x + 1 + r) (q + 2) ≠ 0) :
    binomialBoundary p r q x - binomialBoundary p r q (x + 1) =
      Ring.choose (x + 1 + p) q / Ring.choose (x + 1 + r) (q + 2) := by
  have hC := choose_upper_step (x + p + 1) q
  have hB := choose_upper_step (x + r) (q + 2)
  have hq : (q : K) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero q)
  have hrx : x + r + 1 = x + 1 + r := by ring
  have hpx : x + p + 1 = x + 1 + p := by ring
  rw [hrx] at hB
  rw [hpx] at hC
  unfold binomialBoundary
  rw [hpx]
  push_cast at hB
  field_simp
  linear_combination
    (x + p - q + 1) * Ring.choose (x + 1 + p) q * hB -
      (x + r - q) * Ring.choose (x + r) (q + 2) * hC

/-- The binomial identity stated after (11), with arbitrary upper parameters
and explicit nonzero denominators. -/
theorem binomial_quotient_sum (p r : K) (q m : ℕ) (hpr : p - r + 1 ≠ 0)
    (hv : ∀ n ≤ m, Ring.choose ((n : K) + r) (q + 2) ≠ 0) :
    ∑ n ∈ Finset.range m,
      Ring.choose ((n : K) + 1 + p) q / Ring.choose ((n : K) + 1 + r) (q + 2) =
      binomialBoundary p r q 0 - binomialBoundary p r q (m : K) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (fun n hn => hv n (by omega))]
    have hs := binomial_boundary_step p r q (m : K) hpr (hv m (by omega))
      (by simpa using hv (m + 1) (by omega))
    push_cast
    linear_combination -hs

/-- The first boundary term in the paper's displayed form. -/
theorem binomialBoundary_zero (p r : K) (q : ℕ) (hpr : p - r + 1 ≠ 0)
    (h0 : Ring.choose r (q + 2) ≠ 0) (h1 : Ring.choose (r + 1) (q + 2) ≠ 0) :
    binomialBoundary p r q 0 =
      (r + 1) * (p - q + 1) * Ring.choose (p + 1) q /
        (((q : K) + 1) * (p - r + 1) * Ring.choose (r + 1) (q + 2)) := by
  have h := choose_upper_step r (q + 2)
  have hq : (q : K) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero q)
  unfold binomialBoundary
  simp only [zero_add]
  field_simp
  push_cast at h
  linear_combination (p - q + 1) * Ring.choose (p + 1) q * h

section Alternating

omit [CharZero K]

open Polynomial

/-- For `(-1)^k * choose(ν, k)`, the backward convention uses
`p = 1`, `q = X - C (ν + 1)`, and `r = X`. The constant certificate
equation is `-ν * c = 1`, so solving it requires a parameter condition. -/
theorem alternating_binomial_operator_const (ν c : K) :
    operator (X - C (ν + 1)) X (C c) = C (-ν * c) := by
  simp only [operator_apply, map_sub, taylor_X, taylor_C, map_add, map_one,
    map_mul, map_neg, taylor_one]
  ring

/-- The generic certificate is valid only away from `ν = 0`.
This condition comes from solving for a coefficient, even though `p = 1`. -/
theorem alternating_binomial_certificate (ν : K) (hν : ν ≠ 0) :
    operator (X - C (ν + 1)) X (C (-ν⁻¹)) = 1 := by
  rw [alternating_binomial_operator_const]
  simp [hν]

/-- The condition is necessary for any polynomial certificate, not merely
for the constant ansatz. At `ν = 0`, evaluating the equation at zero gives
`0 = 1`. This does not exclude computing the finite sum separately. -/
theorem alternating_binomial_polynomial_solution_iff (ν : K) :
    (∃ f : K[X], operator (X - C (ν + 1)) X f = 1) ↔ ν ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩ rfl
    have h := congrArg (fun P : K[X] => P.eval 0) hf
    simp at h
  · intro hν
    exact ⟨C (-ν⁻¹), alternating_binomial_certificate ν hν⟩

/-- The finite sum retains its exceptional value at `n = 0`.
Mathlib's integer identity supplies both branches without dividing by `n`. -/
theorem alternating_binomial_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : K) ^ k * (n.choose k : K) =
      if n = 0 then 1 else 0 := by
  simpa using congrArg (Int.castRingHom K) (Int.alternating_sum_range_choose (n := n))

end Alternating

end Gosper
