module

public import SympyProofs.Binomial.Naive

/-!
# Verification of binary-splitting binomial evaluation

The nonnegative-upper path builds numerator/denominator pairs recursively,
using a loop for blocks of at most 128 factors and gcd cancellation at each
merge. The negative-upper path retains the product loop and final factorial
division. The evaluators use integer arithmetic, with natural loop bounds;
rational quotients appear only in the correctness proofs.
-/

@[expose] public section

namespace SympyBinomial.BinarySplitting

open scoped Std.WP

/-- Build a numerator/denominator pair for the half-open interval `[lo, hi)`. -/
def product (d : ℤ) (lo hi : ℕ) : ℤ × ℤ := Id.run do
  if hi - lo ≤ 128 then
    let mut p : ℤ := 1
    let mut q : ℤ := 1
    for i in [lo:hi] do
      p := p * (d + i)
      q := q * i
    let g : ℤ := p.gcd q
    return (p.fdiv g, q.fdiv g)
  else
    let mid := (lo + hi) / 2
    let mut (plo, qlo) := product d lo mid
    let mut (phi, qhi) := product d mid hi
    let g : ℤ := plo.gcd qhi
    plo := plo.fdiv g
    qhi := qhi.fdiv g
    let g : ℤ := phi.gcd qlo
    phi := phi.fdiv g
    qlo := qlo.fdiv g
    return (plo * phi, qlo * qhi)
termination_by hi - lo
decreasing_by all_goals omega

/-- The binary-splitting evaluator for a nonnegative lower argument. -/
def evalCore (n : ℤ) (k : ℕ) : ℤ := Id.run do
  let mut k := k
  if 0 ≤ n then
    if (k : ℤ) > n then
      return 0
    else if (k : ℤ) > n.fdiv 2 then
      k := (n - k).toNat
    let d := n - k
    let (p, q) := product d 1 (k + 1)
    return p.fdiv q
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

private theorem cancel_spec (p q : ℤ) (hq : 0 < q) :
    let g : ℤ := p.gcd q
    0 < q.fdiv g ∧
      (p.fdiv g : ℚ) / (q.fdiv g : ℚ) = (p : ℚ) / (q : ℚ) := by
  dsimp only
  have hg : (0 : ℤ) < p.gcd q := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_right p (ne_of_gt hq)
  have hqmul := Int.fdiv_mul_cancel (Int.gcd_dvd_right p q)
  refine ⟨by nlinarith, ?_⟩
  rw [Naive.exact_division_cast _ _ (ne_of_gt hg) (Int.gcd_dvd_left p q),
    Naive.exact_division_cast _ _ (ne_of_gt hg) (Int.gcd_dvd_right p q)]
  have hg' : (p.gcd q : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hg
  simp [div_div_div_cancel_right₀ hg']

private def factor (d : ℤ) (i : ℕ) : ℚ := ((d : ℚ) + i) / i

/-- Every recursive block has a positive denominator and the expected quotient. -/
private theorem product_spec (d : ℤ) (lo hi : ℕ) (hlo : 0 < lo) :
    0 < (product d lo hi).2 ∧
      ((product d lo hi).1 : ℚ) / ((product d lo hi).2 : ℚ) =
        ((List.range' lo (hi - lo)).map (factor d)).prod := by
  by_cases hcut : hi - lo ≤ 128
  · generalize he : product d lo hi = result
    apply Std.WP.Id.of_run_eq_wp he
    unfold product
    simp only [hcut, ↓reduceIte, Id.run]
    vcgen invariants
    · fun pref _ (p, q) => 0 < q ∧ (p : ℚ) / (q : ℚ) = (pref.map (factor d)).prod
    case vc1 => simp
    case vc2 =>
      rename_i p q hinv
      have hc := cancel_spec p q hinv.1
      exact ⟨hc.1, hc.2.trans (by simpa using hinv.2)⟩
    case vc3 =>
      rename_i pref i suff hs p q hinv
      have hmem : i ∈ List.range' lo (hi - lo) := by
        have : i ∈ ForIn.toList [lo:hi] := by rw [hs]; simp
        simpa using this
      have hi0 : (0 : ℤ) < i := by
        obtain ⟨j, _, rfl⟩ := List.mem_range'.mp hmem
        omega
      dsimp only
      constructor
      · exact mul_pos hinv.1 hi0
      · simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
          List.prod_cons, List.prod_nil, mul_one, Int.cast_mul, Int.cast_add, Int.cast_natCast]
        rw [mul_div_mul_comm, hinv.2]
        rfl
  · have hleft := product_spec d lo ((lo + hi) / 2) hlo
    have hright := product_spec d ((lo + hi) / 2) hi (by omega)
    rw [product]
    simp only [hcut, ↓reduceIte]
    dsimp only [Id.run, Bind.bind, Pure.pure]
    have hc₁ := cancel_spec (product d lo ((lo + hi) / 2)).1
      (product d ((lo + hi) / 2) hi).2 hright.1
    have hc₂ := cancel_spec (product d ((lo + hi) / 2) hi).1
      (product d lo ((lo + hi) / 2)).2 hleft.1
    refine ⟨mul_pos hc₂.1 hc₁.1, ?_⟩
    have hrange : List.range' lo (hi - lo) =
        List.range' lo ((lo + hi) / 2 - lo) ++
          List.range' ((lo + hi) / 2) (hi - (lo + hi) / 2) := by
      have hm : lo + ((lo + hi) / 2 - lo) = (lo + hi) / 2 := by omega
      have hn : ((lo + hi) / 2 - lo) + (hi - (lo + hi) / 2) = hi - lo := by omega
      simpa only [hm, hn] using
        (List.range'_append_1 (s := lo) (m := (lo + hi) / 2 - lo)
          (n := hi - (lo + hi) / 2)).symm
    rw [hrange, List.map_append, List.prod_append]
    push_cast
    have cross (a b c e : ℚ) : a * c / (b * e) = a / e * (c / b) := by ring
    rw [cross, hc₁.2, hc₂.2, ← hleft.2, ← hright.2]
    ring
termination_by hi - lo
decreasing_by all_goals omega

private theorem factors_eq_choose (d : ℤ) (k : ℕ) :
    ((List.range' 1 k).map (factor d)).prod = (Ring.choose (d + k) k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range'_concat, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, one_mul, factor, Nat.cast_add, Nat.cast_one]
    rw [← mul_div_assoc]
    apply (div_eq_iff (by positivity : (1 + (k : ℚ)) ≠ 0)).2
    have h := congrArg (fun a : ℤ => (a : ℚ)) (Naive.choose_step_mul (d + k) k)
    push_cast at h
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h

/-- The full block represents an integer binomial, so the final division is exact. -/
theorem product_full_spec (d : ℤ) (k : ℕ) :
    0 < (product d 1 (k + 1)).2 ∧
      (product d 1 (k + 1)).1 =
        Ring.choose (d + k) k * (product d 1 (k + 1)).2 := by
  obtain ⟨hq, hratio⟩ := product_spec d 1 (k + 1) (by omega)
  refine ⟨hq, ?_⟩
  simp only [Nat.add_sub_cancel, factors_eq_choose] at hratio
  have hq' : ((product d 1 (k + 1)).2 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have heq := (div_eq_iff hq').mp hratio
  exact_mod_cast heq

theorem product_div_exact (d : ℤ) (k : ℕ) :
    (product d 1 (k + 1)).2 ∣ (product d 1 (k + 1)).1 := by
  rw [(product_full_spec d k).2]
  exact dvd_mul_left _ _

theorem product_div_eq_choose (d : ℤ) (k : ℕ) :
    (product d 1 (k + 1)).1.fdiv (product d 1 (k + 1)).2 = Ring.choose (d + k) k := by
  obtain ⟨hq, hp⟩ := product_full_spec d k
  rw [hp, Int.mul_fdiv_cancel _ (ne_of_gt hq)]

theorem evalCore_eq_choose (n : ℤ) (k : ℕ) : evalCore n k = choose n (k : ℤ) := by
  by_cases hn : 0 ≤ n
  · unfold evalCore
    simp only [hn, ↓reduceIte, Id.run, Pure.pure]
    split_ifs with hkn hhalf
    · rw [choose_int_eq]
      have hlt : n.toNat < k := by omega
      simp [hn, Nat.choose_eq_zero_of_lt hlt]
    · rw [product_div_eq_choose, sub_add_cancel]
      lift n to ℕ using hn with n
      have hk : k ≤ n := by omega
      rw [Ring.choose_natCast, choose_natCast_natCast]
      congr 1
      simpa [Int.toNat_sub] using Nat.choose_symm hk
    · rw [product_div_eq_choose, sub_add_cancel, choose_natCast]
  · simpa only [evalCore, Naive.evalCore, hn, ↓reduceIte] using Naive.evalCore_eq_choose n k

theorem evalCore_eq_naive (n : ℤ) (k : ℕ) : evalCore n k = Naive.evalCore n k := by
  rw [evalCore_eq_choose, Naive.evalCore_eq_choose]

/-- The binary-splitting implementation agrees with the naive evaluator on all integer inputs. -/
theorem eval_eq_naive (n k : ℤ) : eval n k = Naive.eval n k := by
  simp only [eval, Naive.eval, evalCore_eq_naive]

/-- For every integer pair, the binary-splitting model equals our integer specification. -/
theorem eval_eq_choose (n k : ℤ) : eval n k = choose n k := by
  rw [eval_eq_naive, Naive.eval_eq_choose]

end SympyBinomial.BinarySplitting
