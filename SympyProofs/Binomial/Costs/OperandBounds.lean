module

public import SympyProofs.Binomial.Algorithms.PrimeExponentCorrectness
public import SympyProofs.Python.Cost.Width

/-!
# Operand bounds for the complete prime-exponent algorithm

These bounds concern valid inputs `k ≤ n`. A prime-power factor is at most `n`,
although the product can have `n + 1` bits. The sum of factor widths is linear
in `n`; this is the size parameter needed by a product-tree cost proof.
-/

@[expose] public section

namespace SympyBinomial.PrimeExponent

open Python.Cost Python.Cost.Models

/-- Width of the nonnegative upper argument, with one bit for zero. -/
def inputWidth (n : ℕ) : ℕ := width (n : ℤ)

@[simp] theorem inputWidth_eq (n : ℕ) : inputWidth n = n.log2 + 1 := by
  simp [inputWidth, width_eq_log2_succ]

theorem inputWidth_pos (n : ℕ) : 1 ≤ inputWidth n := one_le_width _

/-- Kummer's carry bound controls the *value* of each prime power. -/
theorem primePower_le (n k p : ℕ) (hn : 0 < n) :
    p ^ (n.choose k).factorization p ≤ n := Nat.pow_factorization_choose_le hn

theorem primePower_width_le (n k p : ℕ) (hn : 0 < n) :
    width ((p ^ (n.choose k).factorization p : ℕ) : ℤ) ≤ inputWidth n := by
  apply width_mono
  simpa using primePower_le n k p hn

/-- Quotient loops need at most the input width, for every prime divisor. -/
theorem quotient_iterations_le (n p : ℕ) (hp : 2 ≤ p) :
    Nat.log p n + 1 ≤ inputWidth n := by
  rw [inputWidth_eq, Nat.log2_eq_log_two]
  by_cases hn : n = 0
  · simp [hn]
  apply Nat.add_le_add_right
  apply Nat.le_log_of_pow_le (by omega)
  exact (Nat.pow_le_pow_left hp _).trans (Nat.pow_log_le_self p hn)

private theorem pow_sum_log_le_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 0 < x) :
    2 ^ (xs.map (Nat.log 2)).sum ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
    exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (by have := hxs x (by simp); omega))
      (ih (fun x hx => hxs x (by simp [hx])))

/-- Positive factors have total width at most the product's logarithm plus their count. -/
theorem sum_width_le_log_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 0 < x) :
    (xs.map (fun x : ℕ => width (x : ℤ))).sum ≤ Nat.log 2 xs.prod + xs.length := by
  have hlog : (xs.map (Nat.log 2)).sum ≤ Nat.log 2 xs.prod :=
    Nat.le_log_of_pow_le (by omega) (pow_sum_log_le_prod xs hxs)
  have he : (xs.map (fun x : ℕ => width (x : ℤ))).sum =
      (xs.map (Nat.log 2)).sum + xs.length := by
    clear hlog hxs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, width_eq_log2_succ,
        Int.natAbs_natCast, Nat.log2_eq_log_two] at *
      omega
  omega

/-- The argument applies to any partial/product-tree factor list whose product divides
`choose n k`, including omission of the factor two and factors equal to one. -/
theorem factorBits_le (n k : ℕ) (hk : k ≤ n) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, 0 < x) (hprod : xs.prod ∣ n.choose k) :
    (xs.map (fun x : ℕ => width (x : ℤ))).sum ≤ n + xs.length := by
  have hbound : n.choose k ≤ 2 ^ n := by
    exact Nat.choose_le_two_pow n k
  have hp : xs.prod ≤ 2 ^ n :=
    (Nat.le_of_dvd (Nat.choose_pos hk) hprod).trans hbound
  have hl : Nat.log 2 xs.prod ≤ n := by
    have h := Nat.log_mono_right (b := 2) hp
    simpa using h
  exact (sum_width_le_log_prod xs hxs).trans (Nat.add_le_add_right hl _)

/-- The final integer is also bounded, uniformly over the lower argument. -/
theorem result_width_le (n k : ℕ) : width (n.choose k : ℤ) ≤ n + 1 := by
  have h := width_mono (x := (n.choose k : ℤ)) (y := (2 ^ n : ℕ))
    (by simpa using Nat.choose_le_two_pow n k)
  simpa [width_eq_log2_succ, Nat.log2_eq_log_two] using h

/-- Bound on a power-operation event, accounting for the result width as well as the inputs. -/
theorem primePower_schoolbook_le (n k p : ℕ) (hn : 0 < n) (hp : p ≤ n) :
    schoolbook (.integer ⟨.pow, [p, (n.choose k).factorization p],
      (p ^ (n.choose k).factorization p : ℕ)⟩) ≤ 4 * inputWidth n ^ 3 := by
  let W := inputWidth n
  have hw : 1 ≤ W := inputWidth_pos n
  have ha : width (p : ℤ) ≤ W := width_mono (by simpa using hp)
  have hb : width ((n.choose k).factorization p : ℤ) ≤ W := by
    apply width_mono
    simpa using (Nat.factorization_choose_le_log (n := n) (k := k) (p := p)).trans
      (Nat.log_le_self p n)
  have hr : width ((p ^ (n.choose k).factorization p : ℕ) : ℤ) ≤ W :=
    primePower_width_le n k p hn
  have hm : max (width (p : ℤ)) (width ((p ^ (n.choose k).factorization p : ℕ) : ℤ)) ≤ W :=
    max_le ha hr
  change 1 + (2 * width ((n.choose k).factorization p : ℤ) + 1) *
    max (width (p : ℤ)) (width ((p ^ (n.choose k).factorization p : ℕ) : ℤ)) *
    max (width (p : ℤ)) (width ((p ^ (n.choose k).factorization p : ℕ) : ℤ)) ≤ 4 * W ^ 3
  calc
    _ ≤ 1 + (2 * W + 1) * W * W := by gcongr
    _ ≤ 4 * W ^ 3 := by
      have hsq : W ≤ W * W := by nlinarith
      have hc : W * W ≤ W * W*W := Nat.le_mul_of_pos_right _ hw
      nlinarith

/-- Each Legendre summand is a carry, hence zero or one. -/
theorem quotient_carry (n k q : ℕ) (hk : k ≤ n) (hq : 0 < q) :
    0 ≤ ((n / q : ℕ) : ℤ) - (k / q : ℕ) - ((n - k) / q : ℕ) ∧
      ((n / q : ℕ) : ℤ) - (k / q : ℕ) - ((n - k) / q : ℕ) ≤ 1 := by
  have h := Nat.add_div (a := k) (b := n - k) hq
  rw [Nat.add_sub_of_le hk] at h
  split_ifs at h <;> omega

/-- After this many divisions the upper quotient is zero, for any prime base. -/
theorem quotient_zero_at_width (n p : ℕ) (hp : 2 ≤ p) :
    n / p ^ inputWidth n = 0 := by
  apply Nat.div_eq_of_lt
  have h : n < 2 ^ inputWidth n := by
    rw [inputWidth_eq]
    exact Nat.lt_log2_self
  exact h.trans_le (Nat.pow_le_pow_left hp _)

/-- Charge all prime powers, even the exponent-zero ones that Python skips.
This dominates the actual power calls once the quotient-loop invariant is connected. -/
def primePowerCharges (n k : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (n + 1), if p.Prime then
    schoolbook (.integer ⟨.pow, [p, (n.choose k).factorization p],
      (p ^ (n.choose k).factorization p : ℕ)⟩) else 0

theorem primePowerCharges_le (n k : ℕ) :
    primePowerCharges n k ≤ (n + 1) * (4 * inputWidth n ^ 3) := by
  by_cases hn : n = 0
  · subst n
    norm_num [primePowerCharges, inputWidth_eq]
  · unfold primePowerCharges
    calc
      _ ≤ ∑ _p ∈ Finset.range (n + 1), 4 * inputWidth n ^ 3 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs
        · exact primePower_schoolbook_le n k p (by omega) (by simpa using hp)
        · exact Nat.zero_le _
      _ = _ := by simp [Nat.mul_comm]


/-- Dividing a positive integer by at least two removes at least one bit. -/
theorem size_div_lt (a p : ℕ) (ha : 0 < a) (hp : 2 ≤ p) :
    (a / p).size < a.size := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero
    (show a.size ≠ 0 from (Nat.size_pos.mpr ha).ne')
  rw [hs, Nat.lt_succ_iff, Nat.size_le]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mpr
  have h := Nat.lt_size_self a
  rw [hs, pow_succ] at h
  exact h.trans_le (Nat.mul_le_mul_left _ hp)

/-- Repeated quotient states retain the original carry interpretation. -/
theorem quotient_next (n p t : ℕ) : n / p ^ t / p = n / p ^ (t+1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- A carry state remains a carry state after floor division. -/
theorem carry_div (a b c p : ℕ) (hp : 0 < p)
    (hlo : b+c ≤ a) (hhi : a ≤ b+c+1) :
    b/p+c/p ≤ a/p ∧ a/p ≤ b/p+c/p+1 := by
  have ha := Nat.mod_add_div a p
  have hb := Nat.mod_add_div b p
  have hc := Nat.mod_add_div c p
  have hma := Nat.mod_lt a hp
  have hmb := Nat.mod_lt b hp
  have hmc := Nat.mod_lt c hp
  constructor
  · by_contra h
    have hq : a/p+1 ≤ b/p+c/p := by omega
    have hm := Nat.mul_le_mul_left p hq
    nlinarith only [ha, hb, hc, hlo, hhi, hma, hmb, hmc, hm, Nat.zero_le (a%p), Nat.zero_le (b%p), Nat.zero_le (c%p)]
  · by_contra h
    have hq : b/p+c/p+2 ≤ a/p := by omega
    have hm := Nat.mul_le_mul_left p hq
    nlinarith only [ha, hb, hc, hlo, hhi, hma, hmb, hmc, hm, Nat.zero_le (a%p), Nat.zero_le (b%p), Nat.zero_le (c%p)]
end SympyBinomial.PrimeExponent
