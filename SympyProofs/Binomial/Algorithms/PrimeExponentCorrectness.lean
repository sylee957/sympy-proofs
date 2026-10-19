module

public import SympyProofs.Binomial.Algorithms.PrimeExponent
public import SympyProofs.Binomial.Algorithms.ByteSieveGeneratorCorrectness
public import Mathlib.Data.Nat.Choose.Factorization

/-!
# Correctness of prime-exponent binomial evaluation

The component theorems verify the power-of-two exponent and balanced
multiplication. `primeExponents_eq_choose` proves the complete imperative kernel
correct, using the verified byte sieve and a quotient-loop invariant. The loop's
termination measure is `a`: division by a visited prime strictly decreases it
whenever the guard holds.
The final signed exponent is nonnegative, so its conversion to `Nat` discards
nothing. The proof applies to every lawful `PythonByteArray` carrier.
-/

@[expose] public section

namespace SympyBinomial.PrimeExponent

open Python.Bitwise
open scoped Std.WP

variable (B : Type) [PythonByteArray B]

private theorem factorial_two (n : ℕ) :
    n.factorial.factorization 2 + (Nat.digits 2 n).sum = n := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have hd := Nat.digit_sum_le 2 n
  simp only [Nat.reduceSub, one_mul] at h
  omega

/-- The bit-count expression is the exact multiplicity of two, not an estimate. -/
theorem valuation_eq_factorization (n k : ℕ) (hk : k ≤ n) :
    valuation n k = ((n.choose k).factorization 2 : ℤ) := by
  have hc := congrArg (fun m : ℕ => m.factorization 2)
    (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.factorization_mul (Nat.mul_ne_zero (Nat.choose_ne_zero hk)
      (Nat.factorial_ne_zero k)) (Nat.factorial_ne_zero (n - k)),
    Nat.factorization_mul (Nat.choose_ne_zero hk) (Nat.factorial_ne_zero k),
    Finsupp.add_apply] at hc
  have hn := factorial_two n
  have hk' := factorial_two k
  have hnk := factorial_two (n - k)
  simp only [valuation, bitCount_eq_digit_sum]
  omega

theorem valuation_nonneg (n k : ℕ) (hk : k ≤ n) : 0 ≤ valuation n k := by
  rw [valuation_eq_factorization n k hk]
  positivity

private theorem balancedFactors_rec_eq_prod (factors : Array ℕ) (leaf : ℕ)
    (hleaf : 0 < leaf) (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ factors.size) :
    balancedFactors.rec factors leaf hleaf lo hi = (factors.extract lo hi).toList.prod := by
  by_cases hcut : hi - lo ≤ leaf
  · rw [balancedFactors.rec]
    simp [hcut, Python.Math.prod_eq_prod, Subarray.toList_eq,
      Nat.min_eq_left hhi, Nat.min_eq_left hlo]
  · have hm₁ : lo ≤ (lo + hi) / 2 := by omega
    have hm₂ : (lo + hi) / 2 ≤ hi := by omega
    rw [balancedFactors.rec]
    simp only [hcut, ↓reduceIte, Id.run, Pure.pure]
    rw [balancedFactors_rec_eq_prod factors leaf hleaf lo ((lo + hi) / 2) hm₁ (by omega),
      balancedFactors_rec_eq_prod factors leaf hleaf ((lo + hi) / 2) hi hm₂ hhi]
    rw [← List.prod_append, ← Array.toList_append, Array.extract_append_extract]
    simp [Nat.min_eq_left hm₁, Nat.max_eq_right hm₂]
termination_by hi - lo
decreasing_by all_goals omega

/-- Every positive leaf size gives the product of the entire input sequence. -/
theorem balancedFactors_eq_prod (factors : Array ℕ) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) :
    balancedFactors factors leaf hleaf = factors.toList.prod := by
  simpa [balancedFactors] using
    balancedFactors_rec_eq_prod factors leaf hleaf 0 factors.size (by omega) (by omega)

/-- The signed difference of factorial multiplicities is the binomial multiplicity. -/
theorem factorial_exponent_sub (n k p : ℕ) (hk : k ≤ n) :
    (n.factorial.factorization p : ℤ) - k.factorial.factorization p -
      (n - k).factorial.factorization p = ((n.choose k).factorization p : ℤ) := by
  have hc := congrArg (fun m : ℕ => m.factorization p)
    (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.factorization_mul (Nat.mul_ne_zero (Nat.choose_ne_zero hk)
      (Nat.factorial_ne_zero k)) (Nat.factorial_ne_zero (n - k)),
    Nat.factorization_mul (Nat.choose_ne_zero hk) (Nat.factorial_ne_zero k),
    Finsupp.add_apply] at hc
  omega

/-- Multiplying the odd prime powers and restoring the power of two gives the binomial. -/
theorem prime_product_eq_choose (n k : ℕ) (hk : k ≤ n) :
    (∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 2),
      p ^ (n.choose k).factorization p) <<< (valuation n k).toNat = n.choose k := by
  simp only [valuation_eq_factorization n k hk, Int.toNat_natCast, Nat.shiftLeft_eq]
  by_cases hn : 2 ≤ n
  · have h2 : 2 ∈ Finset.range (n + 1) := by simp; omega
    have hprod :
        (∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 2),
          p ^ (n.choose k).factorization p) =
        ∏ p ∈ (Finset.range (n + 1)).erase 2, p ^ (n.choose k).factorization p := by
      apply Finset.prod_subset
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        simp [Finset.mem_erase, hp.2.2, hp.1]
      · intro p hp hnot
        have hnp : ¬p.Prime := by
          intro hprime
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hp, hprime,
            (Finset.mem_erase.mp hp).1⟩)
        simp [Nat.factorization_eq_zero_of_not_prime _ hnp]
    rw [hprod, Finset.prod_erase_mul _ _ h2, Nat.prod_pow_factorization_choose n k hk]
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> interval_cases k <;> norm_num [Nat.factorization_one]

private theorem factorial_exponent_step (n p : ℕ) (hp : p.Prime) :
    n.factorial.factorization p = n / p + (n / p).factorial.factorization p := by
  have hp2 := hp.two_le
  have h₁ := Nat.sub_one_mul_factorization_factorial (n := n) hp
  have h₂ := Nat.sub_one_mul_factorization_factorial (n := n / p) hp
  have hl₁ := Nat.digit_sum_le p n
  have hl₂ := Nat.digit_sum_le p (n / p)
  have hd : (Nat.digits p n).sum = n % p + (Nat.digits p (n / p)).sum := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [Nat.digits_def' hp2 (by omega), List.sum_cons]
  have hmod := Nat.mod_add_div n p
  have he₁ : (p - 1) * n.factorial.factorization p + (Nat.digits p n).sum = n := by omega
  have he₂ : (p - 1) * (n / p).factorial.factorization p + (Nat.digits p (n / p)).sum = n / p := by omega
  have hp' : p - 1 + 1 = p := by omega
  nlinarith

private theorem prime_of_visit {n p : ℕ} {pref suff : List ℕ}
    (h : (List.range (n + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2)) =
      pref ++ p :: suff) : p.Prime := by
  have hm : p ∈ (List.range (n + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2)) :=
    h ▸ List.mem_append_right _ (by simp)
  have hx : p.Prime ∧ p ≠ 2 := by simpa using (List.mem_filter.mp hm).2
  exact hx.1

private theorem exponent_finish (n k p a b c : ℕ) (e : ℤ)
    (ha : a = 0) (hb : b ≤ a) (hc : c ≤ a)
    (he : e + (a.factorial.factorization p : ℤ) - b.factorial.factorization p -
      c.factorial.factorization p = ((n.choose k).factorization p : ℤ)) :
    e = ((n.choose k).factorization p : ℤ) := by
  have hb0 : b = 0 := by omega
  have hc0 : c = 0 := by omega
  simpa [ha, hb0, hc0] using he

private theorem oddPrimes_product_choose (n k : ℕ) (hk : k ≤ n) :
    ((((List.range (n + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2))).map
      (fun p => p ^ (n.choose k).factorization p)).prod) <<< (valuation n k).toNat =
        n.choose k := by
  rw [← List.prod_toFinset _ (List.nodup_range.filter _)]
  have hr : (List.range (n + 1)).toFinset = Finset.range (n + 1) := by ext; simp
  simpa [hr] using prime_product_eq_choose n k hk

/-- The imperative kernel computes the binomial for every valid input and every lawful bytearray carrier. -/
theorem primeExponents_eq_choose (n k : ℕ) (hk : k ≤ n) :
    primeExponents B n k = n.choose k := by
  generalize he : primeExponents B n k = result
  unfold primeExponents at he
  simp (config := { zeta := false, beta := false, iota := false, proj := false }) only
    [ByteSieve.oddPrimesGenerator_forIn] at he
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ factors => factors.toList.prod =
      (pref.map (fun p => p ^ (n.choose k).factorization p)).prod
  · by
      rename_i outerPref p outerSuff hs acc hacc
      exact fun exit (a, b, c, e) =>
        b ≤ a ∧ c ≤ a ∧
        e + (a.factorial.factorization p : ℤ) - b.factorial.factorization p -
          c.factorial.factorization p = ((n.choose k).factorization p : ℤ) ∧
        (exit = true → a = 0)
  · Std.WP.Variant.ofMeasure (fun (a, _, _, _) => a)
  case vc1 => simp_all
  case vc2 => simp [factors]
  case vc3 =>
    rename_i factors hinv
    rw [balancedFactors_eq_prod]
    rw [hinv]
    simpa using oddPrimes_product_choose n k hk
  case vc4 =>
    rename_i pref p suff hs factors hinv
    exact ⟨hk, Nat.sub_le n k, by simpa [c] using factorial_exponent_sub n k p hk, by simp⟩
  case vc5 =>
    rename_i pref p suff hs old hprod a b c e hinv _ _ hne
    have heq := exponent_finish n k p a b c e
      (hinv.2.2.2 rfl) hinv.1 hinv.2.1 hinv.2.2.1
    simp only [factors, Array.toList_push, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, heq, Int.toNat_natCast, List.map_append, List.map_cons, List.map_nil, hprod]
  case vc6 =>
    rename_i pref p suff hs old hprod a b c e hinv _ _ he0
    have heq := exponent_finish n k p a b c e
      (hinv.2.2.2 rfl) hinv.1 hinv.2.1 hinv.2.2.1
    have hz : (n.choose k).factorization p = 0 := by omega
    simp [List.map_append, List.prod_append, hprod, hz]
  case vc7 =>
    rename_i pref p suff hs old hprod initialC a0 b0 c0 e0 measure hinv _ _ hne
    have hp := prime_of_visit hs
    simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Assertion.NondetFun.evalsTo_pure,
      Lean.Order.ofProp_prop_eq, Lean.Order.meet_prop_eq_and,
      Bool.false_eq_true, false_implies, and_true] at hinv
    dsimp only [a, b, c, e]
    simp only [Std.WP.Variant.evalsBelow_ofMeasure_nat, Lean.Order.ofProp_prop_eq,
      Lean.Order.meet_prop_eq_and, Bool.false_eq_true, false_implies, and_true]
    refine ⟨?_, Nat.div_le_div_right hinv.2.1, Nat.div_le_div_right hinv.2.2.1, ?_⟩
    · rw [← hinv.1]
      exact Nat.div_lt_self (by omega) (by have := hp.two_le; omega)
    · have ha := factorial_exponent_step a0 p hp
      have hb := factorial_exponent_step b0 p hp
      have hc := factorial_exponent_step c0 p hp
      have he := hinv.2.2.2
      rw [ha, hb, hc] at he
      simp only [Int.natCast_add] at he
      linear_combination he
  case vc8 =>
    rename_i pref p suff hs old hprod a b c e measure hinv _ _ ha0
    simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Assertion.NondetFun.evalsTo_pure,
      Lean.Order.ofProp_prop_eq, Lean.Order.meet_prop_eq_and,
      Bool.false_eq_true, false_implies, and_true] at hinv
    exact ⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2, fun _ => by omega⟩

/-- Agreement of the executable nonnegative kernel with our SymPy integer convention. -/
theorem primeExponents_eq_integer_choose (n k : ℕ) (hk : k ≤ n) :
    (primeExponents B n k : ℤ) = SympyBinomial.choose (n : ℤ) (k : ℤ) := by
  rw [primeExponents_eq_choose B n k hk, choose_natCast_natCast]

end SympyBinomial.PrimeExponent
