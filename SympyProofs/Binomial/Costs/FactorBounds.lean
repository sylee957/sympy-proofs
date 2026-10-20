module

public import SympyProofs.Binomial.Costs.OperandBounds
public import SympyProofs.Python.Cost.Asymptotics

/-!
# Global size bounds for the prime-exponent algorithm

The sum of prime-power widths is at most `2n + 1`. This follows from divisibility
of their product into `choose n k`, including the harmless factor-one entries.
The elementary estimate `inputWidth n ^ 3 ≤ 8 * (n + 1)` converts the phase
bounds into a quadratic bound without a prime-number theorem.
-/

@[expose] public section

open Python.Cost Python.Cost.Models

namespace SympyBinomial.PrimeExponent

private theorem cube_le_exp (t : ℕ) : (t + 1) ^ 3 ≤ 8 * 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    by_cases ht : t < 3
    · interval_cases t <;> norm_num
    · have ht3 : 3 ≤ t := by omega
      have hsq : 3 * t ≤ t * t := Nat.mul_le_mul_right t ht3
      have hcube : 3 * (t * t) ≤ t*(t * t) := Nat.mul_le_mul_right (t * t) ht3
      have hstep : (t + 2) ^ 3 ≤ 2 * (t + 1) ^ 3 := by nlinarith
      calc
        (t + 1 + 1) ^ 3 = (t + 2) ^ 3 := by ring
        _ ≤ 2 * (t + 1) ^ 3 := hstep
        _ ≤ 2 * (8 * 2 ^ t) := Nat.mul_le_mul_left 2 ih
        _ = 8 * 2 ^ (t + 1) := by ring

theorem inputWidth_cube_le (n : ℕ) : (inputWidth n) ^ 3 ≤ 8 * (n + 1) := by
  rw [inputWidth_eq]
  have h := cube_le_exp n.log2
  have hp : 2 ^ n.log2 ≤ n + 1 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_add_one 2 n
  nlinarith

/-- Include all bases up to `n`, even the factor-one entries omitted by the algorithm. -/
def factorBits (n k : ℕ) : ℕ :=
  let exponents := (n.choose k).factorization
  ∑ p ∈ Finset.range (n + 1), width ((p ^ exponents p : ℕ) : ℤ)

theorem factorBits_le_upper (n k : ℕ) (hk : k ≤ n) : factorBits n k ≤ 2 * n + 1 := by
  let xs := (List.range (n + 1)).map (fun p => p ^ (n.choose k).factorization p)
  have hx : ∀ x ∈ xs, 0 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    by_cases h : p = 0
    · subst p
      simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 0)]
    · exact Nat.pow_pos (by omega)
  have hr : (List.range (n + 1)).toFinset = Finset.range (n + 1) := by ext; simp
  have hprod : xs.prod = n.choose k := by
    dsimp [xs]
    rw [← List.prod_toFinset _ List.nodup_range]
    simpa [hr] using Nat.prod_pow_factorization_choose n k hk
  have h := factorBits_le n k hk xs hx (hprod ▸ dvd_refl _)
  have hsum : (xs.map (fun x : ℕ => width (x : ℤ))).sum = factorBits n k := by
    dsimp [xs, factorBits]
    rw [List.map_map, ← List.sum_toFinset _ List.nodup_range]
    simp [hr]
  rw [hsum] at h
  simpa [xs, two_mul, Nat.add_assoc] using h

theorem inputWidth_le (n : ℕ) : inputWidth n ≤ n + 1 := by
  rw [inputWidth_eq, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1

end SympyBinomial.PrimeExponent
