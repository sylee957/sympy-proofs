module

public import SympyProofs.Binomial.Basic
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Kummer's theorem for binomial coefficients

For a prime `p` and `k ≤ n`, the exponent of `p` in `n.choose k` counts the
base-`p` carries in `k + (n - k)`, or equivalently the borrows in `n - k`.
The carry and digit-sum theorems come from mathlib. This file identifies carries
with the remainder comparisons used by Goetgheluck's algorithm and proves their
digit-by-digit borrow recurrence.

Positions start at `1`: position `i` is the boundary after the lowest `i` digits.
The largest possible position is `Nat.log p n`. The hypotheses `p.Prime` and
`k ≤ n` are essential to the valuation statements; a zero binomial does not
have a finite prime multiplicity.
-/

@[expose] public section

namespace SympyBinomial.Kummer

/-- Number of carry boundaries in the base-`p` addition of `a` and `b`. -/
def carryCount (p a b : ℕ) : ℕ :=
  ((Finset.Ico 1 (Nat.log p (a + b) + 1)).filter
    (fun i => p ^ i ≤ a % p ^ i + b % p ^ i)).card

/-- Number of borrow boundaries in `n - k`, used when `k ≤ n` and `2 ≤ p`. -/
def borrowCount (p n k : ℕ) : ℕ :=
  ((Finset.Ico 1 (Nat.log p n + 1)).filter
    (fun i => n % p ^ i < k % p ^ i)).card

/-- Adding the lower blocks overflows exactly when subtracting them needs a borrow. -/
theorem carry_iff_borrow {n k q : ℕ} (hk : k ≤ n) (hq : 0 < q) :
    q ≤ k % q + (n - k) % q ↔ n % q < k % q := by
  have hkq := Nat.mod_lt k hq
  have hdq := Nat.mod_lt (n - k) hq
  have hmod : n % q = (k % q + (n - k) % q) % q := by
    rw [← Nat.add_mod]
    congr 1
    omega
  by_cases hcarry : q ≤ k % q + (n - k) % q
  · have hlt : k % q + (n - k) % q - q < q := by omega
    rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have hlt : k % q + (n - k) % q < q := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmod
    omega

/-- The outgoing borrow is determined by the current digits and the incoming borrow. -/
theorem borrow_succ_iff {p n k i : ℕ} (hp : 0 < p) :
    n % p ^ (i + 1) < k % p ^ (i + 1) ↔
      n / p ^ i % p <
        k / p ^ i % p + (if n % p ^ i < k % p ^ i then 1 else 0) := by
  have hq : 0 < p ^ i := pow_pos hp i
  have hn := Nat.mod_lt n hq
  have hk := Nat.mod_lt k hq
  rw [pow_succ, Nat.mod_mul, Nat.mod_mul]
  split_ifs with hborrow
  · constructor
    · intro h
      by_contra hnot
      have hmul := Nat.mul_le_mul_left (p ^ i) (show
        k / p ^ i % p + 1 ≤ n / p ^ i % p by omega)
      have hle : k % p ^ i + p ^ i * (k / p ^ i % p) ≤
          n % p ^ i + p ^ i * (n / p ^ i % p) := calc
        _ ≤ p ^ i + p ^ i * (k / p ^ i % p) :=
          Nat.add_le_add_right (Nat.le_of_lt hk) _
        _ = p ^ i * (k / p ^ i % p + 1) := by simp [Nat.mul_add, Nat.add_comm]
        _ ≤ p ^ i * (n / p ^ i % p) := hmul
        _ ≤ _ := Nat.le_add_left _ _
      exact (Nat.not_lt_of_ge hle) h
    · intro h
      have hmul := Nat.mul_le_mul_left (p ^ i) (show
        n / p ^ i % p ≤ k / p ^ i % p by omega)
      omega
  · constructor
    · intro h
      have hlt : n / p ^ i % p < k / p ^ i % p := by
        by_contra hnot
        have hmul := Nat.mul_le_mul_left (p ^ i) (show
          k / p ^ i % p ≤ n / p ^ i % p by omega)
        omega
      simpa using hlt
    · intro h
      have hmul := Nat.mul_le_mul_left (p ^ i) (show
        n / p ^ i % p + 1 ≤ k / p ^ i % p by simpa using h)
      calc
        _ < p ^ i + p ^ i * (n / p ^ i % p) := Nat.add_lt_add_right hn _
        _ = p ^ i * (n / p ^ i % p + 1) := by simp [Nat.mul_add, Nat.add_comm]
        _ ≤ p ^ i * (k / p ^ i % p) := hmul
        _ ≤ _ := Nat.le_add_left _ _

/-- Carry counting and borrow counting describe the same events. -/
theorem carryCount_eq_borrowCount {p n k : ℕ} (hp : 0 < p) (hk : k ≤ n) :
    carryCount p k (n - k) = borrowCount p n k := by
  have hsum : k + (n - k) = n := by omega
  simp only [carryCount, borrowCount, hsum]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact carry_iff_borrow hk (pow_pos hp i)

/-- Kummer's theorem: prime multiplicity equals the number of carries. -/
theorem factorization_choose_eq_carryCount {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    (n.choose k).factorization p = carryCount p k (n - k) := by
  have hsum : k + (n - k) = n := by omega
  simpa only [carryCount, hsum] using
    Nat.factorization_choose hp hk (Nat.lt_succ_self (Nat.log p n))

/-- Kummer's theorem in Goetgheluck's borrow-counting form. -/
theorem factorization_choose_eq_borrowCount {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    (n.choose k).factorization p = borrowCount p n k := by
  rw [factorization_choose_eq_carryCount hp hk, carryCount_eq_borrowCount hp.pos hk]

/-- The same theorem using mathlib's natural-valued `p`-adic valuation. -/
theorem padicValNat_choose_eq_borrowCount {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    padicValNat p (n.choose k) = borrowCount p n k := by
  rw [← Nat.factorization_def _ hp, factorization_choose_eq_borrowCount hp hk]

/-- The digit-sum form of Kummer's theorem, with natural subtraction. -/
theorem sub_one_mul_factorization_choose {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    (p - 1) * (n.choose k).factorization p =
      (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  let : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  exact sub_one_mul_padicValNat_choose_eq_sub_sum_digits hk

/-- At base two, digit sums are population counts and the factor `p - 1` disappears. -/
theorem factorization_choose_two {n k : ℕ} (hk : k ≤ n) :
    (n.choose k).factorization 2 =
      (Nat.digits 2 k).sum + (Nat.digits 2 (n - k)).sum - (Nat.digits 2 n).sum := by
  simpa using sub_one_mul_factorization_choose Nat.prime_two hk

/-- Kummer's theorem applies to our integer binomial on the nonzero natural triangle. -/
theorem padicValInt_choose_natCast {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    padicValInt p (SympyBinomial.choose (n : ℤ) (k : ℤ)) = borrowCount p n k := by
  rw [SympyBinomial.choose_natCast_natCast, padicValInt, Int.natAbs_natCast]
  exact padicValNat_choose_eq_borrowCount hp hk

/-- For upper argument `-(m+1)`, the sign has no effect on prime multiplicity. -/
theorem padicValInt_choose_neg_natCast_succ (m k : ℕ) {p : ℕ} (hp : p.Prime) :
    padicValInt p (SympyBinomial.choose (-((m : ℤ) + 1)) (k : ℤ)) =
      carryCount p k m := by
  rw [SympyBinomial.choose_neg_natCast_succ, padicValInt]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul, Int.natAbs_natCast]
  rw [← Nat.factorization_def _ hp,
    factorization_choose_eq_carryCount hp (Nat.le_add_left k m)]
  simp

end SympyBinomial.Kummer
