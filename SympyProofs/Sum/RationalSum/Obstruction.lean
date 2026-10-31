module

public import SympyProofs.Sum.RationalSum.PartialFractions
public import SympyProofs.Sum.Gosper.Summability

/-! A rational difference with a shift-free denominator has no proper part. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A shift-free denominator cannot support a nonpolynomial rational difference. -/
theorem polynomial_of_summable_shiftFree (A B : Polynomial K) (hB : B ≠ 0)
    (hs : ShiftlessDecomposition.ShiftFree B)
    (h : ∃ G : RatFunc K, Gosper.rationalShift 1 G - G = (A : RatFunc K) / B) :
    ∃ C : Polynomial K, (A : RatFunc K) / B = C := by
  have hc : Gosper.ShiftCoprime (taylor (-1) B) B := by
    intro j
    have h := (hs (j + 1) (by omega)).map (taylorAlgHom (-1 : K)).toRingHom
    change IsCoprime (taylor (-1) B) (taylor (-1) (taylor ((j + 1 : ℤ) : K) B)) at h
    have hh : (-1 : K) + ((j + 1 : ℤ) : K) = (j : K) := by push_cast; ring
    simpa only [taylor_taylor, hh] using h
  obtain ⟨G, hG⟩ := h
  have he : ∃ f : RatFunc K, Gosper.RationalSolution A (taylor (-1) B) B f := by
    refine ⟨Gosper.rationalShift 1 G, ?_⟩
    unfold Gosper.RationalSolution
    simp only [taylor_taylor, add_neg_cancel, taylor_zero,
      Gosper.rationalShift_add, neg_add_cancel, Gosper.rationalShift_zero]
    have hB' : (B : RatFunc K) ≠ 0 := by simpa using hB
    have he := (div_eq_iff hB').mp hG.symm
    simp only [RatFunc.coePolynomial] at he
    linear_combination he
  obtain ⟨f, hf⟩ := (Gosper.rational_solution_iff_polynomial A _ _ hc).mp he
  refine ⟨f - taylor (-1) f, ?_⟩
  simp only [Gosper.operator_apply, taylor_taylor, add_neg_cancel, taylor_zero] at hf
  rw [← hf, ← mul_sub]
  simp only [RatFunc.coePolynomial, map_mul]
  exact mul_div_cancel_left₀ _ (by simpa using hB)

omit [CharZero K] in
/-- Combine the digits at the powers of one base into a single numerator. -/
def powerNumerator (b : Polynomial K) {n : ℕ} (a : Fin n → Polynomial K) : Polynomial K :=
  ∑ i, a i * b ^ (n - 1 - i.val)

omit [CharZero K] in
theorem powerNumerator_fraction (b : Polynomial K) (hb : b ≠ 0)
    {n : ℕ} (a : Fin n → Polynomial K) :
    (powerNumerator b a : RatFunc K) / (b : RatFunc K) ^ n =
      ∑ i, (a i : RatFunc K) / (b : RatFunc K) ^ (i.val + 1) := by
  simp only [powerNumerator, RatFunc.coePolynomial, map_sum, map_mul, map_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have he : n = (n - 1 - i.val) + (i.val + 1) := by omega
  conv_lhs => rhs; rw [he, pow_add]
  have hb' : algebraMap K[X] (RatFunc K) b ≠ 0 := by simpa using hb
  field_simp

omit [CharZero K] in
theorem powerNumerator_degree (b : Polynomial K) (hb : b.Monic)
    {n : ℕ} (a : Fin n → Polynomial K) (ha : ∀ i, (a i).degree < b.degree) :
    (powerNumerator b a).degree < (b ^ n).degree := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_iff_ne_bot.mpr
    (degree_ne_bot.mpr (pow_ne_zero _ hb.ne_zero)))).mpr
  intro i _
  have hlt : (a i * b ^ (n - 1 - i.val)).degree < (b ^ (n - 1 - i.val + 1)).degree := by
    rw [pow_succ', (hb.pow _).degree_mul, (hb.pow _).degree_mul]
    exact (WithBot.add_lt_add_iff_right
      (degree_ne_bot.mpr (pow_ne_zero _ hb.ne_zero))).mpr (ha i)
  exact hlt.trans_le (degree_le_of_dvd (pow_dvd_pow b (by omega)) (pow_ne_zero _ hb.ne_zero))

omit [CharZero K] in
theorem powerNumerator_eq_zero (b : Polynomial K) (hb : b.Monic)
    {n : ℕ} (a : Fin n → Polynomial K) (ha : ∀ i, (a i).degree < b.degree)
    (hz : powerNumerator b a = 0) : ∀ i, a i = 0 := by
  have he : (0 : Polynomial K) * b ^ n + ∑ i : Fin n, a i.rev * b ^ i.val =
      0 * b ^ n + ∑ i : Fin n, (0 : Polynomial K) * b ^ i.val := by
    simp only [zero_mul, Finset.sum_const_zero, zero_add]
    rw [← hz]
    unfold powerNumerator
    exact Fintype.sum_equiv ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
      _ _ (fun i => by simp only [Equiv.coe_fn_mk, Fin.val_rev]; congr 2; omega)
  have h := (quo_mul_pow_add_sum_rem_mul_pow_unique hb
    (fun i => ha i.rev)
    (fun i => by simpa using (WithBot.bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hb.ne_zero))) he).2
  intro i
  simpa using congrFun h i.rev

section Fractions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
theorem fraction_sum (F A : ι → Polynomial K) (hm : ∀ i, (F i).Monic) :
    ∑ i, (A i : RatFunc K) / (F i : RatFunc K) =
      ((∑ i, A i * ∏ j ∈ Finset.univ.erase i, F j : Polynomial K) : RatFunc K) /
        ((∏ i, F i : Polynomial K) : RatFunc K) := by
  simp only [RatFunc.coePolynomial, map_sum, map_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]
  symm
  exact mul_div_mul_right _ _ (by
    simpa only [map_zero] using (IsFractionRing.injective K[X] (RatFunc K)).ne
      (monic_prod_of_monic (Finset.univ.erase i) F (fun j _ => hm j)).ne_zero)

/-- Proper fractions at mutually shift-coprime bases cannot sum to a nonzero
rational difference. Powers of the bases need not be square-free. -/
theorem fractions_eq_zero_of_summable (F A : ι → Polynomial K)
    (hm : ∀ i, (F i).Monic)
    (hc : Pairwise (fun i j => IsCoprime (F i) (F j)))
    (hs : ShiftlessDecomposition.ShiftFree (∏ i, F i))
    (ha : ∀ i, (A i).degree < (F i).degree)
    (h : ∃ G : RatFunc K, Gosper.rationalShift 1 G - G =
      ∑ i, (A i : RatFunc K) / (F i : RatFunc K)) : ∀ i, A i = 0 := by
  let M := ∏ i, F i
  let T := ∑ i, A i * ∏ j ∈ Finset.univ.erase i, F j
  have hM : M.Monic := monic_prod_of_monic _ F (fun i _ => hm i)
  rw [fraction_sum F A hm] at h
  obtain ⟨C, hC⟩ := polynomial_of_summable_shiftFree T M hM.ne_zero hs h
  have he : T = C * M := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa only [RatFunc.coePolynomial, map_mul] using
      (div_eq_iff (show (M : RatFunc K) ≠ 0 by simpa using hM.ne_zero)).mp hC
  have hu := quo_mul_prod_add_sum_rem_mul_prod_unique
    (fun i (_ : i ∈ Finset.univ) => hm i)
    (fun i _ j _ hij => hc hij)
    (q₁ := 0) (q₂ := C) (r₁ := A) (r₂ := fun _ => 0)
    (fun i _ => ha i)
    (fun i _ => by simpa using (WithBot.bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (hm i).ne_zero)))
    (by simpa only [zero_mul, zero_add, Finset.sum_const_zero, add_zero] using he)
  exact fun i => hu.2 i (Finset.mem_univ i)

end Fractions
end Gosper.RationalSum
