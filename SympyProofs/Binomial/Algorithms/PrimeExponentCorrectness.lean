module

public import SympyProofs.Binomial.Algorithms.PrimeExponent
public import SympyProofs.Binomial.Algorithms.ByteSieveGeneratorCorrectness
public import SympyProofs.Binomial.Kummer
public import Mathlib.Data.Nat.Choose.Factorization

/-!
# Correctness of prime-exponent binomial evaluation

The component theorems verify the power-of-two exponent and balanced
multiplication. `primeExponents_eq_choose` proves the complete imperative kernel
correct, using the verified byte sieve and a quotient-loop invariant. The loop's
termination measure is `a`: division by a visited prime strictly decreases it
whenever the guard holds.
Prime divisors are nonzero, and power/shift exponents are nonnegative, so every
integer operation is used in its specified Python domain. The proof applies to
every lawful `PythonInt` and `PythonByteArray` carrier.
-/

@[expose] public section

namespace SympyBinomial.PrimeExponent

open PythonInt
open scoped Std.WP

variable (I B : Type) [PythonInt I] [PythonByteArray B]

private theorem factorial_two (n : ℕ) :
    n.factorial.factorization 2 + (Nat.digits 2 n).sum = n := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have hd := Nat.digit_sum_le 2 n
  simp only [Nat.reduceSub, one_mul] at h
  omega

/-- The bit-count expression is the exact multiplicity of two, not an estimate. -/
theorem valuation_eq_factorization (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) :
    toInt (valuation I n k) = (((toNat n).choose (toNat k)).factorization 2 : ℤ) := by
  have hn0 : 0 ≤ toInt n := by omega
  have hkN : (toNat k) ≤ (toNat n) := by unfold toNat; omega
  have hc := congrArg (fun m : ℕ => m.factorization 2)
    (Nat.choose_mul_factorial_mul_factorial hkN)
  simp only [Nat.factorization_mul (Nat.mul_ne_zero (Nat.choose_ne_zero hkN)
      (Nat.factorial_ne_zero (toNat k))) (Nat.factorial_ne_zero ((toNat n) - (toNat k))),
    Nat.factorization_mul (Nat.choose_ne_zero hkN) (Nat.factorial_ne_zero (toNat k)),
    Finsupp.add_apply] at hc
  have hn := factorial_two (toNat n)
  have hk' := factorial_two (toNat k)
  have hnk := factorial_two ((toNat n) - (toNat k))
  have hna : (toInt n).natAbs = (toNat n) := by unfold toNat; omega
  have hka : (toInt k).natAbs = (toNat k) := by unfold toNat; omega
  have hda : (toInt n - toInt k).natAbs = (toNat n) - (toNat k) := by
    unfold toNat; omega
  simp only [valuation, Value.bitCount, toInt_sub, toInt_add, toInt_bitCount, hna, hka, hda]
  omega

theorem valuation_nonneg (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) : 0 ≤ toInt (valuation I n k) := by
  rw [valuation_eq_factorization I n k hk0 hk]
  positivity

/-- The Python bit-count expression counts binary borrows, by Kummer's theorem. -/
theorem valuation_eq_borrowCount (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) :
    toInt (valuation I n k) = (Kummer.borrowCount 2 (toNat n) (toNat k) : ℤ) := by
  have hkN : toNat k ≤ toNat n := by unfold toNat; omega
  rw [valuation_eq_factorization I n k hk0 hk,
    Kummer.factorization_choose_eq_borrowCount Nat.prime_two hkN]

private theorem balancedFactors_rec_eq_prod (factors : Array I) (leaf : ℕ)
    (hleaf : 0 < leaf) (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ factors.size) :
    toInt (balancedFactors.rec I factors leaf hleaf lo hi) =
      ((factors.extract lo hi).toList.map toInt).prod := by
  by_cases hcut : hi - lo ≤ leaf
  · rw [balancedFactors.rec]
    simp [hcut, Python.Math.toInt_prod, Subarray.toList_eq,
      Nat.min_eq_left hhi, Nat.min_eq_left hlo]
  · have hm₁ : lo ≤ (lo + hi) / 2 := by omega
    have hm₂ : (lo + hi) / 2 ≤ hi := by omega
    rw [balancedFactors.rec]
    simp only [hcut, ↓reduceIte, Id.run, Pure.pure, toInt_mul]
    rw [balancedFactors_rec_eq_prod factors leaf hleaf lo ((lo + hi) / 2) hm₁ (by omega),
      balancedFactors_rec_eq_prod factors leaf hleaf ((lo + hi) / 2) hi hm₂ hhi]
    rw [← List.prod_append, ← List.map_append, ← Array.toList_append, Array.extract_append_extract]
    simp [Nat.min_eq_left hm₁, Nat.max_eq_right hm₂]
termination_by hi - lo
decreasing_by all_goals omega

/-- Every positive leaf size gives the product of the entire input sequence. -/
theorem balancedFactors_eq_prod (factors : Array I) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) :
    toInt (balancedFactors I factors leaf hleaf) = (factors.toList.map toInt).prod := by
  simpa [balancedFactors] using
    balancedFactors_rec_eq_prod I factors leaf hleaf 0 factors.size (by omega) (by omega)

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
      p ^ (n.choose k).factorization p) <<< (n.choose k).factorization 2 = n.choose k := by
  simp only [Nat.shiftLeft_eq]
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

/-- One quotient step in Legendre's formula for a factorial multiplicity. -/
theorem factorial_exponent_step (n p : ℕ) (hp : p.Prime) :
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

private theorem exponent_finish (n k p : ℕ) (a b c e : I)
    (ha : toInt a = 0) (hb0 : 0 ≤ toInt b) (hc0 : 0 ≤ toInt c)
    (hb : toInt b ≤ toInt a) (hc : toInt c ≤ toInt a)
    (he : toInt e + ((toNat a).factorial.factorization p : ℤ) -
      (toNat b).factorial.factorization p - (toNat c).factorial.factorization p =
        ((n.choose k).factorization p : ℤ)) :
    toInt e = ((n.choose k).factorization p : ℤ) := by
  have hb' : toInt b = 0 := by omega
  have hc' : toInt c = 0 := by omega
  simpa [toNat, ha, hb', hc'] using he

private theorem oddPrimes_product_choose (n k : ℕ) (hk : k ≤ n) :
    ((((List.range (n + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2))).map
      (fun p => p ^ (n.choose k).factorization p)).prod) <<< (n.choose k).factorization 2 =
        n.choose k := by
  rw [← List.prod_toFinset _ (List.nodup_range.filter _)]
  have hr : (List.range (n + 1)).toFinset = Finset.range (n + 1) := by ext; simp
  simpa [hr] using prime_product_eq_choose n k hk

/-- The imperative kernel is correct for every lawful integer and bytearray carrier. -/
theorem primeExponents_eq_choose (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) :
    toInt (primeExponents I B n k) = ((toNat n).choose (toNat k) : ℤ) := by
  have hn0 : 0 ≤ toInt n := by omega
  have hkN : (toNat k) ≤ (toNat n) := by unfold toNat; omega
  generalize he : primeExponents I B n k = result
  unfold primeExponents at he
  simp (config := { zeta := false, beta := false, iota := false, proj := false }) only
    [ByteSieve.oddPrimesGenerator_forIn] at he
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ factors => (factors.toList.map toInt).prod =
      ((pref.map (fun p => p ^ ((toNat n).choose (toNat k)).factorization p)).prod : ℕ)
  · by
      rename_i outerPref prime outerSuff hs acc hacc
      exact fun exit (a, b, c, e) =>
        0 ≤ toInt a ∧ 0 ≤ toInt b ∧ 0 ≤ toInt c ∧
        toInt b ≤ toInt a ∧ toInt c ≤ toInt a ∧
        toInt e + ((toNat a).factorial.factorization prime : ℤ) -
          (toNat b).factorial.factorization prime - (toNat c).factorial.factorization prime =
            (((toNat n).choose (toNat k)).factorization prime : ℤ) ∧
        (exit = true → toInt a = 0)
  · Std.WP.Variant.ofMeasure (fun (a, _, _, _) => toNat a)
  all_goals clear he
  case vc1 =>
    rename_i hz
    have hz' : toInt k = 0 := by simpa using hz
    simp [toNat, hz']
  case vc2 => simp [factors]
  case vc3 =>
    rename_i factors hinv
    rw [toInt_shiftLeft _ _ (valuation_nonneg I n k hk0 hk), balancedFactors_eq_prod I,
      hinv, valuation_eq_factorization I n k hk0 hk, Int.toNat_natCast]
    have h := congrArg (fun x : ℕ => (x : ℤ))
      (oddPrimes_product_choose (toNat n) (toNat k) hkN)
    simpa [Nat.shiftLeft_eq] using h
  case vc4 =>
    rename_i pref prime suff hs factors hinv
    have hc : toNat (n - k) = toNat n - toNat k := by
      simp only [toNat, toInt_sub]
      omega
    refine ⟨hn0, hk0, ?_, hk, ?_, ?_, by simp⟩
    · simpa [c] using sub_nonneg.mpr hk
    · simpa [c] using sub_le_self (toInt n) hk0
    · simpa [c, hc] using factorial_exponent_sub (toNat n) (toNat k) prime hkN
  case vc5 =>
    rename_i pref prime suff hs old hprod a b c e hinv _ _ hne
    have heq := exponent_finish I (toNat n) (toNat k) prime a b c e
      (hinv.2.2.2.2.2.2 rfl) hinv.2.1 hinv.2.2.1 hinv.2.2.2.1 hinv.2.2.2.2.1
      hinv.2.2.2.2.2.1
    have he0 : 0 ≤ toInt e := by rw [heq]; positivity
    simp [factors, List.map_append, toInt_pow _ _ he0, p, heq, hprod]
  case vc6 =>
    rename_i pref prime suff hs old hprod a b c e hinv _ _ he0
    have heq := exponent_finish I (toNat n) (toNat k) prime a b c e
      (hinv.2.2.2.2.2.2 rfl) hinv.2.1 hinv.2.2.1 hinv.2.2.2.1 hinv.2.2.2.2.1
      hinv.2.2.2.2.2.1
    have he0' : toInt e = 0 := by simpa using he0
    have hz : ((toNat n).choose (toNat k)).factorization prime = 0 := by omega
    simpa [List.map_append, hz] using hprod
  case vc7 =>
    rename_i pref prime suff hs old hprod initialC a0 b0 c0 e0 measure hinv _ _ hne
    have hp := prime_of_visit hs
    simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Assertion.NondetFun.evalsTo_pure,
      Lean.Order.ofProp_prop_eq, Lean.Order.meet_prop_eq_and,
      Bool.false_eq_true, false_implies, and_true] at hinv
    rcases hinv with ⟨hm, ha0, hb0, hc0, hba, hca, he⟩
    have hane : toInt a0 ≠ 0 := by simpa using hne
    have hbN : toNat b0 ≤ toNat a0 := by unfold toNat; omega
    have hcN : toNat c0 ≤ toNat a0 := by unfold toNat; omega
    have da := toInt_div_of_nonneg a0 prime ha0 hp.ne_zero
    have db := toInt_div_of_nonneg b0 prime hb0 hp.ne_zero
    have dc := toInt_div_of_nonneg c0 prime hc0 hp.ne_zero
    have na := toNat_div_of_nonneg a0 prime ha0 hp.ne_zero
    have nb := toNat_div_of_nonneg b0 prime hb0 hp.ne_zero
    have nc := toNat_div_of_nonneg c0 prime hc0 hp.ne_zero
    dsimp only [a, b, c, e, p]
    simp only [Std.WP.Variant.evalsBelow_ofMeasure_nat, Lean.Order.ofProp_prop_eq,
      Lean.Order.meet_prop_eq_and, Bool.false_eq_true, false_implies, and_true,
      toInt_add, toInt_sub, da, db, dc, na, nb, nc]
    refine ⟨?_, Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _, ?_, ?_, ?_⟩
    · rw [← hm]
      exact Nat.div_lt_self (by unfold toNat; omega) (by have := hp.two_le; omega)
    · exact_mod_cast Nat.div_le_div_right hbN
    · exact_mod_cast Nat.div_le_div_right hcN
    · have ha := factorial_exponent_step (toNat a0) prime hp
      have hb := factorial_exponent_step (toNat b0) prime hp
      have hc := factorial_exponent_step (toNat c0) prime hp
      rw [ha, hb, hc] at he
      simp only [Int.natCast_add] at he
      linear_combination he
  case vc8 =>
    rename_i pref prime suff hs old hprod a b c e measure hinv _ _ ha0
    simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Assertion.NondetFun.evalsTo_pure,
      Lean.Order.ofProp_prop_eq, Lean.Order.meet_prop_eq_and,
      Bool.false_eq_true, false_implies, and_true] at hinv
    have ha : toInt a = 0 := by simpa using ha0
    exact ⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1,
      hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2, fun _ => ha⟩

/-- Agreement of the abstract integer kernel with our SymPy integer convention. -/
theorem primeExponents_eq_integer_choose (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) :
    toInt (primeExponents I B n k) = SympyBinomial.choose (toInt n) (toInt k) := by
  rw [primeExponents_eq_choose I B n k hk0 hk,
    toInt_eq_natCast n (by omega), toInt_eq_natCast k hk0, choose_natCast_natCast]

end SympyBinomial.PrimeExponent
