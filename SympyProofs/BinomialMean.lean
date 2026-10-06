import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open Finset

namespace BinomialMean

/-- The first weighted binomial identity, before substituting `q = 1 - p`. -/
theorem weighted_binomial_succ (n : ℕ) (p q : ℝ) :
    (∑ k ∈ range (n + 2),
      (k : ℝ) * (n + 1).choose k * p ^ k * q ^ (n + 1 - k)) =
      (n + 1 : ℕ) * p * (p + q) ^ n := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  calc
    (∑ k ∈ range (n + 1),
        ((k + 1 : ℕ) : ℝ) * (n + 1).choose (k + 1) *
          p ^ (k + 1) * q ^ (n + 1 - (k + 1))) =
        ∑ k ∈ range (n + 1),
          ((n + 1 : ℕ) : ℝ) * p * (p ^ k * q ^ (n - k) * n.choose k) := by
      apply Finset.sum_congr rfl
      intro k _
      have h : ((k + 1 : ℕ) : ℝ) * (n + 1).choose (k + 1) =
          ((n + 1 : ℕ) : ℝ) * n.choose k := by
        exact_mod_cast (show (k + 1) * (n + 1).choose (k + 1) =
          (n + 1) * n.choose k by
            simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k).symm)
      rw [h, Nat.add_sub_add_right, pow_succ]
      ring
    _ = ((n + 1 : ℕ) : ℝ) * p * (p + q) ^ n := by
      rw [← Finset.mul_sum, ← add_pow]

/-- The finite sum is `n * p` for every real `p`; no convergence condition is needed. -/
theorem binomial_mean (n : ℕ) (p : ℝ) :
    (∑ k ∈ range (n + 1),
      (k : ℝ) * n.choose k * p ^ k * (1 - p) ^ (n - k)) = (n : ℝ) * p := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [show p + (1 - p) = 1 by ring] using weighted_binomial_succ n p (1 - p)

end BinomialMean
