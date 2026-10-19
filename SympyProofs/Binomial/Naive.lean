module

public import SympyProofs.Binomial.Basic
public import Std.Tactic.Do
public import Std.WP

/-!
# Verification of SymPy's naive integer binomial evaluation

This models the pure-Python integer paths, excluding the optional GMP backend.
The nonnegative-upper path divides at every iteration; the negative-upper path
multiplies first and divides by the factorial at the end. Both paths return `ℤ`.
The proofs show that every division is exact, including agreement with SymPy's
symbolic `/ factorial(k)` in the negative-upper path.

The public `eval` accepts `n k : ℤ`; `evalCore` requires `k : ℕ` after `eval`
has checked the zero guards. The symmetry assignment converts `n - k` to `ℕ`
only after checking `k ≤ n`.
-/

@[expose] public section

namespace SympyBinomial.Naive

open scoped Std.WP

set_option experimental.vcgen true

/-- The naive evaluator for a nonnegative lower argument. -/
def evalCore (n : ℤ) (k : ℕ) : ℤ := Id.run do
  let mut k := k
  if 0 ≤ n then
    if (k : ℤ) > n then
      return 0
    else if (k : ℤ) > n.fdiv 2 then
      k := (n - k).toNat
    let mut d := n - k
    let mut result : ℤ := 1
    for i in [1:k + 1] do
      d := d + 1
      result := (result * d).fdiv (i : ℤ)
    return result
  else
    let mut d := n - k
    let mut result : ℤ := 1
    for _i in [1:k + 1] do
      d := d + 1
      result := result * d
    return result.fdiv (k.factorial : ℤ)

/-- The integer evaluator, including early returns and zero guards. -/
def eval (n k : ℤ) : ℤ := Id.run do
  let d := n - k
  if k = 0 ∨ (0 ≤ n ∧ d = 0) then
    return 1
  if k - 1 = 0 ∨ (0 ≤ n ∧ d - 1 = 0) then
    return n
  if k < 0 ∨ (0 ≤ n ∧ d < 0) then
    return 0
  return evalCore n k.toNat

/-- The identity making each division in the naive loop exact. -/
theorem choose_step_mul (n : ℤ) (k : ℕ) :
    Ring.choose n k * (n + 1) = Ring.choose (n + 1) (k + 1) * (k + 1 : ℤ) := by
  have h := Ring.choose_smul_choose (n + 1) (n := k + 1) (k := 1) (by omega)
  simpa [nsmul_eq_mul, mul_comm] using h.symm

/-- The multiply-and-divide step discards no remainder. -/
theorem choose_step_exact (n : ℤ) (k : ℕ) :
    (k + 1 : ℤ) ∣ Ring.choose n k * (n + 1) := by
  rw [choose_step_mul]
  exact dvd_mul_left _ _

private theorem choose_step_div (n : ℤ) (k : ℕ) :
    (Ring.choose n k * (n + 1)).fdiv (k + 1 : ℤ) = Ring.choose (n + 1) (k + 1) := by
  rw [choose_step_mul]
  exact Int.mul_fdiv_cancel _ (by omega)

/-- Exact integer division agrees with SymPy's symbolic rational division. -/
theorem exact_division_cast (p q : ℤ) (hq : q ≠ 0) (h : q ∣ p) :
    (p.fdiv q : ℚ) = (p : ℚ) / (q : ℚ) := by
  obtain ⟨a, rfl⟩ := h
  rw [Int.mul_fdiv_cancel_left _ hq, Int.cast_mul]
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  field_simp

private theorem range_index {k i : ℕ} {pref suff : List ℕ}
    (h : ForIn.toList [1:k + 1] = pref ++ i :: suff) : i = pref.length + 1 := by
  have h' : List.range' 1 k = pref ++ i :: suff := by simpa using h
  obtain ⟨j, _, hp, ht⟩ := List.range'_eq_append_iff.mp h'
  rw [hp]
  have hh := List.range'_eq_cons_iff.mp ht.symm
  simp only [List.length_range']
  omega

private theorem choose_reflected (n k : ℤ) (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) :
    Ring.choose n (n - k).toNat = choose n k := by
  lift n to ℕ using hn with n
  lift k to ℕ using hk with k
  have hkn' : k ≤ n := by omega
  rw [choose_natCast_natCast, Ring.choose_natCast]
  congr 1
  simpa [Int.toNat_sub] using Nat.choose_symm hkn'

theorem evalCore_eq_choose (n : ℤ) (k : ℕ) : evalCore n k = choose n (k : ℤ) := by
  generalize he : evalCore n k = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref suff (d, result) =>
      d = n - (suff.length : ℤ) ∧ result = Ring.choose d pref.length
  · fun pref suff (d, result) =>
      d = n - (suff.length : ℤ) ∧ result = Ring.choose d pref.length
  · fun pref suff (d, result) =>
      d = n - (suff.length : ℤ) ∧ result = (pref.length.factorial : ℤ) * Ring.choose d pref.length
  case vc1 =>
    rename_i hn jp hnk
    change n < (k : ℤ) at hnk
    rw [choose_int_eq]
    have hlt : n.toNat < k := by omega
    simp [hn, Nat.choose_eq_zero_of_lt hlt]
  case vc2 | vc5 | vc8 =>
    simp [d]
  case vc3 =>
    rename_i k0 hn jp hnk hhalf oldD oldResult hi
    have hi' : oldD = n ∧ oldResult = Ring.choose oldD k := by simpa using hi
    rw [hi'.2, hi'.1]
    exact choose_reflected n (k0 : ℤ) hn (by omega) (le_of_not_gt hnk)
  case vc6 =>
    rename_i oldD oldResult hi
    have hi' : oldD = n ∧ oldResult = Ring.choose oldD k := by simpa using hi
    rw [hi'.2, hi'.1, choose_natCast]
  case vc4 | vc7 =>
    rename_i pref i suff hs oldD oldResult hi
    have hi' := range_index hs
    dsimp only [d, result]
    simp only [List.length_cons, List.length_nil, List.length_append, Int.natCast_add,
      Int.natCast_one] at hi ⊢
    refine ⟨by simp [hi.1, sub_add_eq_sub_sub], ?_⟩
    rw [hi.2, hi']
    simpa only [Int.natCast_add, Int.natCast_one] using choose_step_div oldD pref.length
  case vc9 =>
    rename_i oldD oldResult hi
    have hi' : oldD = n ∧ oldResult = (k.factorial : ℤ) * Ring.choose oldD k := by
      simpa using hi
    rw [hi'.2, hi'.1, Int.mul_fdiv_cancel_left _ (by exact_mod_cast k.factorial_ne_zero),
      choose_natCast]
  case vc10 =>
    rename_i pref i suff hs oldD oldResult hi
    dsimp only [d, result]
    simp only [List.length_cons, List.length_nil, List.length_append, Int.natCast_add,
      Int.natCast_one] at hi ⊢
    refine ⟨by simp [hi.1, sub_add_eq_sub_sub], ?_⟩
    rw [hi.2, mul_assoc, choose_step_mul, Nat.factorial_succ]
    push_cast
    ring

private theorem choose_self_of_nonneg (n : ℤ) (hn : 0 ≤ n) : choose n n = 1 := by
  lift n to ℕ using hn with n
  simp [Ring.choose_natCast]

private theorem choose_sub_one_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    choose n (n - 1) = n := by
  lift n to ℕ using hn with n
  cases n with
  | zero => simp [choose]
  | succ n =>
    have h : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [h, choose_natCast_natCast, Nat.choose_succ_self_right]

/-- For every integer pair, the naive source model equals our integer specification. -/
theorem eval_eq_choose (n k : ℤ) : eval n k = choose n k := by
  unfold eval
  dsimp only [Id.run, Bind.bind, Pure.pure]
  split_ifs with hzero hone hout
  · rcases hzero with hk | ⟨hn, hnk⟩
    · subst k; simp
    · have hk : k = n := by omega
      rw [hk, choose_self_of_nonneg n hn]
  · rcases hone with hk | ⟨hn, hnk⟩
    · have hk' : k = 1 := by omega
      rw [hk', choose_one]
    · have hk : k = n - 1 := by omega
      rw [hk, choose_sub_one_of_nonneg n hn]
  · rcases hout with hk | ⟨hn, hnk⟩
    · simp [choose_of_neg _ hk]
    · rw [choose_int_eq]
      have hk : 0 ≤ k := by omega
      have hlt : n.toNat < k.toNat := by omega
      simp [not_lt.mpr hk, hn, Nat.choose_eq_zero_of_lt hlt]
  · have hk : 0 ≤ k := by omega
    simpa only [Int.toNat_of_nonneg hk] using evalCore_eq_choose n k.toNat

end SympyBinomial.Naive
