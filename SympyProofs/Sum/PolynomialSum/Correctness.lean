module

public import SympyProofs.Sum.PolynomialSum.Algorithm
public import Mathlib
public import Std.Tactic.Do
public import Std.WP

/-!
# Soundness of polynomial antidifference

For a polynomial `p` and the computed `q = antidifference p`,
`antidifference_sound` proves `q.comp (1 + X) - q = p` and `q.eval 0 = 0`.
Thus `q(x + 1) - q(x) = p(x)`, and `sum_range` gives
`∑ k ∈ Finset.range n, p.eval k = q.eval n`.

`sum_range_antidifferenceCoefficients` connects the actual output vector directly
to the finite sum after any rational-algebra specialization. Its corollary
`sum_range_antidifferenceCoefficients_apply` allows coefficients to be arbitrary
functions of parameters: evaluating the computed coefficient functions at any
parameter value gives the finite sum of the specialized input. Neither theorem
requires decidable equality on the coefficient rings.

The proof identifies the imperative loop's coefficients with normalized
Bernoulli polynomial primitives (`antidifferenceCoefficients_get`), then proves
that the computed polynomial equals their linear combination
(`antidifference_eq_linear`). Bernoulli numbers are used
only in the linear specification and its proofs.

All results hold over a commutative rational algebra, including polynomial
parameter rings. Specialization commutes with the construction even when the
input degree drops.
-/

@[expose] public section

namespace Gosper.PolynomialSum

open Polynomial hiding bernoulli bernoulli_one
open scoped Std.WP

/-- Entry `(k,n)` of the universal rational summation matrix. The zero row fixes
the constant of summation to zero. All branching is on natural indices. -/
def primitiveCoeff (n k : ℕ) : ℚ :=
  if k = 0 then 0 else
    if k ≤ n + 1 then
      (n + 1 : ℚ)⁻¹ * (bernoulli (n + 1 - k) * (n + 1).choose k)
    else 0

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

noncomputable section

/-- The normalized polynomial primitive of `X ^ n`, with universal rational coefficients. -/
def monomialPrimitive (n : ℕ) : ℚ[X] :=
  (n + 1 : ℚ)⁻¹ • (Polynomial.bernoulli (n + 1) - C (bernoulli (n + 1)))

@[simp] theorem monomialPrimitive_zero : monomialPrimitive 0 = X := by
  norm_num [monomialPrimitive, Polynomial.bernoulli_one, bernoulli_one]

theorem monomialPrimitive_step (n : ℕ) :
    (monomialPrimitive n).comp (1 + X) - monomialPrimitive n = X ^ n := by
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  simp only [monomialPrimitive, smul_comp, sub_comp, C_comp,
    bernoulli_comp_one_add_X, Nat.add_sub_cancel, ← smul_sub]
  rw [show Polynomial.bernoulli (n + 1) + (n + 1) • (X : ℚ[X]) ^ n -
      C (bernoulli (n + 1)) -
      (Polynomial.bernoulli (n + 1) - C (bernoulli (n + 1))) =
      (n + 1) • (X : ℚ[X]) ^ n by abel]
  simp [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hn]

@[simp] theorem monomialPrimitive_eval_zero (n : ℕ) :
    (monomialPrimitive n).eval 0 = 0 := by
  simp [monomialPrimitive]

theorem monomialPrimitive_natDegree_le (n : ℕ) :
    (monomialPrimitive n).natDegree ≤ n + 1 := by
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  refine max_le ?_ (by simp)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [coeff_bernoulli, Nat.not_le.mpr hk]

theorem coeff_monomialPrimitive (n k : ℕ) :
    (monomialPrimitive n).coeff k = primitiveCoeff n k := by
  by_cases hk : k = 0
  · subst k
    simp [primitiveCoeff, coeff_zero_eq_eval_zero]
  · simp [monomialPrimitive, primitiveCoeff, coeff_bernoulli, coeff_C, hk,
      smul_eq_mul, mul_ite]

theorem primitiveCoeff_eq_zero (n k : ℕ) (hk : n + 1 < k) :
    primitiveCoeff n k = 0 := by
  simp [primitiveCoeff, Nat.not_le.mpr hk]

theorem derivative_monomialPrimitive (n : ℕ) :
    (monomialPrimitive n).derivative = Polynomial.bernoulli n := by
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  simp only [monomialPrimitive, derivative_smul, derivative_sub, derivative_C,
    sub_zero, derivative_bernoulli_add_one]
  rw [← C_eq_natCast, ← C_1, ← C_add, ← smul_eq_C_mul, smul_smul]
  simp [hn]

theorem derivative_monomialPrimitive_succ (n : ℕ) :
    (monomialPrimitive (n + 1)).derivative =
      (n + 1 : ℚ) • monomialPrimitive n + C (bernoulli (n + 1)) := by
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  rw [derivative_monomialPrimitive, monomialPrimitive, smul_smul]
  simp [hn]

theorem primitiveCoeff_recurrence (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    primitiveCoeff n k = (n : ℚ) / k * primitiveCoeff (n - 1) (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := congrArg (fun p : ℚ[X] => p.coeff (k - 1))
    (derivative_monomialPrimitive_succ n)
  have hk0 : k - 1 ≠ 0 := by omega
  have hk1 : k - 1 + 1 = k := by omega
  simp only [coeff_derivative, coeff_add, coeff_smul, coeff_C, ite_eq_right hk0,
    add_zero, hk1, coeff_monomialPrimitive, smul_eq_mul] at h
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkcast : ((k - 1 : ℕ) : ℚ) + 1 = k := by exact_mod_cast hk1
  rw [hkcast] at h
  simp only [Nat.succ_sub_one]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hkq).2
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem primitiveCoeff_sum (n : ℕ) (hn : 0 < n) :
    ∑ k : Fin (n + 2), primitiveCoeff n k = 0 := by
  have h := congrArg (Polynomial.eval 0) (monomialPrimitive_step n)
  simp [eval_comp, Nat.ne_of_gt hn] at h
  rw [eval_eq_sum_range' (lt_of_le_of_lt (monomialPrimitive_natDegree_le n)
    (by omega : n + 1 < n + 2))] at h
  simpa [Fin.sum_univ_eq_sum_range, coeff_monomialPrimitive] using h

private theorem range_prefix {N k : ℕ} {pref suff : List ℕ}
    (h : ForIn.toList [:N] = pref ++ k :: suff) : pref.length = k ∧ k < N := by
  have h' : List.range' 0 N = pref ++ k :: suff := by simpa using h
  obtain ⟨l, hl, hp, ht⟩ := List.range'_eq_append_iff.mp h'
  have hc := List.range'_eq_cons_iff.mp ht.symm
  simp only [Nat.mul_one, Nat.zero_add] at hc
  obtain ⟨rfl, hpos, _⟩ := hc
  exact ⟨by simp [hp], by omega⟩

private theorem normalizeRow {N n : ℕ} (hn : n < N)
    (old row : Vector ℚ (N + 1)) (total : ℚ)
    (hold : ∀ k : Fin (N + 1), old[k.val] =
      if n = 0 then 0 else primitiveCoeff (n - 1) k)
    (hrow : ∀ k : Fin (N + 1), row[k.val] =
      if 2 ≤ k.val ∧ k.val ≤ n + 1 then primitiveCoeff n k else old[k.val])
    (htotal : total = ∑ k ∈ Finset.Ico 2 (n + 2), primitiveCoeff n k)
    (k : Fin (N + 1)) :
    (row.set 1 (if n = 0 then 1 else -total) (by omega))[k.val] =
      primitiveCoeff n k := by
  rw [Vector.getElem_set]
  by_cases hk : k.val = 1
  · simp only [hk, ite_true]
    by_cases hn0 : n = 0
    · simp [hn0, primitiveCoeff]
    · rw [ite_eq_right hn0, htotal]
      have hs := primitiveCoeff_sum n (by omega)
      rw [Fin.sum_univ_eq_sum_range, ← Finset.sum_range_add_sum_Ico _
        (by omega : 2 ≤ n + 2)] at hs
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
      have hz : primitiveCoeff n 0 = 0 := by simp [primitiveCoeff]
      rw [hz, zero_add] at hs
      linarith
  · rw [ite_eq_right (Ne.symm hk), hrow k]
    split_ifs with h
    · rfl
    · rw [hold k]
      by_cases hk0 : k.val = 0
      · simp [hk0, primitiveCoeff]
      · have hkn : n + 1 < k.val := by omega
        rw [primitiveCoeff_eq_zero n k hkn]
        split_ifs with hn0
        · rfl
        · exact primitiveCoeff_eq_zero (n - 1) k (by omega)

theorem antidifferenceCoefficients_get {N : ℕ} (a : Fin N → R) (k : ℕ) (hk : k < N + 1) :
    (antidifferenceCoefficients a)[k] = ∑ n : Fin N, a n * algebraMap ℚ R (primitiveCoeff n k) := by
  generalize he : antidifferenceCoefficients a = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ (row, q) =>
      (∀ k : Fin (N + 1), row[k.val] =
        if pref.length = 0 then 0 else primitiveCoeff (pref.length - 1) k) ∧
      (∀ k : Fin (N + 1), q[k.val] = ∑ n ∈ Finset.range pref.length,
        (if h : n < N then a ⟨n, h⟩ else 0) * algebraMap ℚ R (primitiveCoeff n k))
  · by
    rename_i pref n suff hs oldRow oldQ hi
    exact fun pref' _ (row, q, total) =>
      (∀ k : Fin (N + 1), row[k.val] =
        if n + 2 - pref'.length ≤ k.val ∧ k.val ≤ n + 1
        then primitiveCoeff n k else oldRow[k.val]) ∧
      total = ∑ k ∈ Finset.Ico (n + 2 - pref'.length) (n + 2), primitiveCoeff n k ∧
      (∀ k : Fin (N + 1), q[k.val] = oldQ[k.val] +
        if n + 2 - pref'.length ≤ k.val ∧ k.val ≤ n + 1
        then coefficient * algebraMap ℚ R (primitiveCoeff n k) else 0)
  case vc1 => simp +zetaDelta
  case vc2 =>
    rename_i row q hi
    have h := hi.2 ⟨k, hk⟩
    simpa [← Fin.sum_univ_eq_sum_range] using h
  case vc3 =>
    rename_i pref n suff hs oldRow oldQ hi
    have hempty (j : Fin (N + 1)) : ¬ (n + 2 ≤ j.val ∧ j.val ≤ n + 1) := by omega
    simp [hempty]
  case vc4 =>
    rename_i pref n suff hs oldRow oldQ hi currentRow currentQ total hcurrent state
    obtain ⟨hp, hbound⟩ := range_prefix hs
    have hold : ∀ k : Fin (N + 1), oldRow[k.val] =
        if n = 0 then 0 else primitiveCoeff (n - 1) k := by
      simpa only [hp] using hi.1
    have hlen : (ForIn.toList [:n]).length = n := by simp
    simp only [hlen, Nat.add_sub_cancel_left] at hcurrent
    have hrow := normalizeRow hbound oldRow _ _ hold hcurrent.1 hcurrent.2.1
    have hc : c = primitiveCoeff n 1 := by
      simpa only [Vector.getElem_set_self] using hrow ⟨1, by omega⟩
    simp only [List.length_append, List.length_singleton, hp,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    constructor
    · exact hrow
    · intro t
      dsimp only [q]
      rw [Vector.getElem_set, Finset.sum_range_succ, dite_eq_left hbound]
      have hqprev := hi.2 t
      simp only [hp] at hqprev
      rw [← hqprev]
      by_cases ht : 1 = t.val
      · rw [ite_eq_left ht, hcurrent.2.2 ⟨1, by omega⟩]
        simp only [show ¬ (2 ≤ (1 : ℕ) ∧ 1 ≤ n + 1) by omega, ite_false, add_zero]
        simp only [hc, ← ht]
        rfl
      · rw [ite_eq_right ht, hcurrent.2.2 t]
        by_cases hhigh : 2 ≤ t.val ∧ t.val ≤ n + 1
        · rw [ite_eq_left hhigh]
        · have hz : primitiveCoeff n t = 0 := by
            by_cases ht0 : t.val = 0
            · simp [ht0, primitiveCoeff]
            · exact primitiveCoeff_eq_zero n t (by omega)
          simp only [ite_eq_right hhigh, hz, map_zero, mul_zero]
  case vc5 =>
    rename_i pref n suff hs oldRow oldQ hi pref' j suff' hs' currentRow currentQ total hcurrent state
    obtain ⟨hp, hjbound⟩ := range_prefix hs'
    obtain ⟨hpOuter, hnBound⟩ := range_prefix hs
    dsimp only [row, q, total, c, k] at hcurrent ⊢
    have hlow : currentRow[n + 1 - j - 1]'(by omega) =
        primitiveCoeff (n - 1) (n + 1 - j - 1) := by
      rw [hcurrent.1 ⟨n + 1 - j - 1, by omega⟩]
      have h : ¬ (n + 2 - pref'.length ≤ n + 1 - j - 1 ∧
          n + 1 - j - 1 ≤ n + 1) := by omega
      rw [ite_eq_right h, hi.1 ⟨n + 1 - j - 1, by omega⟩, hpOuter,
        ite_eq_right (by omega)]
    have hc : (n : ℚ) / ((n + 1 - j : ℕ) : ℚ) * currentRow[n + 1 - j - 1]'(by omega) =
        primitiveCoeff n (n + 1 - j) := by
      rw [hlow, primitiveCoeff_recurrence n (n + 1 - j) (by omega) (by omega)]
    simp only [hc, List.length_append, List.length_singleton, hp]
    refine ⟨?_, ?_, ?_⟩
    · intro t
      rw [Vector.getElem_set]
      by_cases heq : n + 1 - j = t.val
      · rw [ite_eq_left heq, ite_eq_left (by omega), heq]
      · rw [ite_eq_right heq, hcurrent.1 t]
        have hiff : (n + 2 - pref'.length ≤ t.val ∧ t.val ≤ n + 1) ↔
            (n + 2 - (j + 1) ≤ t.val ∧ t.val ≤ n + 1) := by omega
        simp only [hiff]
    · rw [hcurrent.2.1, hp]
      have hb : n + 2 - (j + 1) = n + 1 - j := by omega
      have ha : n + 2 - j = n + 1 - j + 1 := by omega
      rw [hb, ha, Finset.sum_eq_sum_Ico_succ_bot (by omega : n + 1 - j < n + 2)]
      exact add_comm _ _
    · intro t
      rw [Vector.getElem_set]
      by_cases ht : n + 1 - j = t.val
      · rw [ite_eq_left ht, hcurrent.2.2 ⟨n + 1 - j, by omega⟩]
        have hbefore : ¬ (n + 2 - pref'.length ≤ n + 1 - j ∧ n + 1 - j ≤ n + 1) := by omega
        rw [ite_eq_right hbefore, add_zero, ite_eq_left (by omega)]
        simp only [ht]
      · rw [ite_eq_right ht, hcurrent.2.2 t]
        have hiff : (n + 2 - pref'.length ≤ t.val ∧ t.val ≤ n + 1) ↔
            (n + 2 - (j + 1) ≤ t.val ∧ t.val ≤ n + 1) := by omega
        simp only [hiff]

/-- Proof-only linear specification in terms of Bernoulli polynomial primitives.
The executable `antidifference` is proved equal to this map below. -/
def antidifferenceLinear : R[X] →ₗ[R] R[X] :=
  Polynomial.lsum fun n =>
    (LinearMap.id : R →ₗ[R] R).smulRight ((monomialPrimitive n).map (algebraMap ℚ R))

theorem antidifferenceLinear_apply (p : R[X]) :
    antidifferenceLinear p =
      ∑ n ∈ p.support, p.coeff n • (monomialPrimitive n).map (algebraMap ℚ R) := rfl

@[simp] theorem antidifferenceLinear_monomial (n : ℕ) (a : R) :
    antidifferenceLinear (monomial n a) = a • (monomialPrimitive n).map (algebraMap ℚ R) := by
  simp [antidifferenceLinear, Polynomial.lsum, LinearMap.smulRight_apply]

@[simp] theorem antidifferenceLinear_C (a : R) : antidifferenceLinear (C a) = C a * X := by
  change antidifferenceLinear (monomial 0 a) = C a * X
  rw [antidifferenceLinear_monomial, monomialPrimitive_zero, Polynomial.map_X, smul_eq_C_mul]

/-- The output is an antidifferenceLinear as a polynomial identity. -/
theorem antidifferenceLinear_step (p : R[X]) :
    (antidifferenceLinear p).comp (1 + X) - antidifferenceLinear p = p := by
  rw [antidifferenceLinear_apply, sum_comp, ← Finset.sum_sub_distrib]
  simp_rw [smul_comp, ← smul_sub]
  have hb (n : ℕ) :
      ((monomialPrimitive n).map (algebraMap ℚ R)).comp (1 + X) -
        (monomialPrimitive n).map (algebraMap ℚ R) = X ^ n := by
    simpa [Polynomial.map_sub, Polynomial.map_comp] using
      congrArg (Polynomial.map (algebraMap ℚ R)) (monomialPrimitive_step n)
  simp_rw [hb, smul_eq_C_mul]
  exact p.sum_C_mul_X_pow_eq

@[simp] theorem antidifferenceLinear_eval_zero (p : R[X]) :
    (antidifferenceLinear p).eval 0 = 0 := by
  have hb (n : ℕ) : ((monomialPrimitive n).map (algebraMap ℚ R)).eval 0 = 0 := by
    simpa only [map_zero, monomialPrimitive_eval_zero] using
      (eval_map_apply (p := monomialPrimitive n) (algebraMap ℚ R) 0)
  simp [antidifferenceLinear_apply, eval_finsetSum, hb]

/-- Degree is bounded directly by the input degree; no search bound is supplied. -/
theorem antidifferenceLinear_natDegree_le (p : R[X]) :
    (antidifferenceLinear p).natDegree ≤ p.natDegree + 1 := by
  rw [antidifferenceLinear_apply]
  apply natDegree_sum_le_of_forall_le
  intro n hn
  exact (natDegree_smul_le _ _).trans (natDegree_map_le.trans
    ((monomialPrimitive_natDegree_le n).trans
      (Nat.add_le_add_right (le_natDegree_of_mem_supp n hn) 1)))

/-- Parameter specialization commutes with summation, including degree-dropping cases. -/
theorem antidifferenceLinear_map (f : R →ₐ[ℚ] S) (p : R[X]) :
    (antidifferenceLinear p).map f.toRingHom = antidifferenceLinear (p.map f.toRingHom) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n a =>
    simp only [antidifferenceLinear_monomial, Polynomial.map_monomial, Polynomial.map_smul,
      antidifferenceLinear_monomial, Polynomial.map_map]
    congr 1
    exact congrArg (Polynomial.map · (monomialPrimitive n)) f.comp_algebraMap

/-- The pointwise forward-difference equation. -/
theorem antidifferenceLinear_eval_step (p : R[X]) (x : R) :
    (antidifferenceLinear p).eval (x + 1) - (antidifferenceLinear p).eval x = p.eval x := by
  simpa [eval_comp, add_comm] using congrArg (Polynomial.eval x) (antidifferenceLinear_step p)

/-- The sum on `0 ≤ k < n` is the constructed polynomial evaluated at `n`. -/
theorem sum_range_linear (p : R[X]) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval (k : R) = (antidifferenceLinear p).eval (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := antidifferenceLinear_eval_step p (n : R)
    push_cast
    linear_combination -h

/-- An arbitrary natural interval is handled by subtracting endpoint values. -/
theorem sum_Ico_linear (p : R[X]) (m n : ℕ) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, p.eval (k : R) =
      (antidifferenceLinear p).eval (n : R) - (antidifferenceLinear p).eval (m : R) := by
  rw [Finset.sum_Ico_eq_sub _ hmn, sum_range_linear, sum_range_linear]

/-- Sum after specializing parameters, using the already constructed symbolic output. -/
theorem sum_range_map_linear (f : R →ₐ[ℚ] S) (p : R[X]) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval₂ f.toRingHom (k : S) =
      (antidifferenceLinear p).eval₂ f.toRingHom (n : S) := by
  simpa only [← antidifferenceLinear_map, eval_map] using sum_range_linear (p.map f.toRingHom) n

/-- Polynomial parameter expressions can be evaluated at arbitrary values,
without nonvanishing assumptions or degree-preservation hypotheses. -/
theorem sum_range_parameters_linear {ι : Type*} (p : (MvPolynomial ι ℚ)[X])
    (σ : ι → S) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval₂ (MvPolynomial.aeval σ).toRingHom (k : S) =
      (antidifferenceLinear p).eval₂ (MvPolynomial.aeval σ).toRingHom (n : S) :=
  sum_range_map_linear (MvPolynomial.aeval σ) p n

/-- Every output coefficient of the abstract construction is the explicit matrix product. -/
theorem coeff_antidifferenceLinear_ofFn [DecidableEq R] {N : ℕ} (a : Fin N → R) (k : ℕ) :
    (antidifferenceLinear (Polynomial.ofFn N a)).coeff k =
      ∑ n : Fin N, a n * algebraMap ℚ R (primitiveCoeff n k) := by
  rw [ofFn_eq_sum_monomial, map_sum, finsetSum_coeff]
  simp [coeff_monomialPrimitive]

/-- Correctness of the executable coefficient-vector algorithm. -/
theorem ofFn_antidifferenceCoefficients [DecidableEq R] {N : ℕ} (a : Fin N → R) :
    Polynomial.ofFn (N + 1) (fun k => (antidifferenceCoefficients a)[k.val]) =
      antidifferenceLinear (Polynomial.ofFn N a) := by
  ext k
  rw [coeff_antidifferenceLinear_ofFn]
  by_cases hk : k < N + 1
  · simp [ofFn_coeff_eq_val_of_lt _ hk, antidifferenceCoefficients_get]
  · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt hk)]
    symm
    apply Finset.sum_eq_zero
    intro n _
    rw [primitiveCoeff_eq_zero n k (by omega), map_zero, mul_zero]

/-- The polynomial-input algorithm agrees with the linear specification,
independently of any degree drops under later specialization. -/
theorem antidifference_eq_linear [DecidableEq R] (p : R[X]) :
    antidifference p = antidifferenceLinear p := by
  rw [antidifference, ofFn_antidifferenceCoefficients]
  congr 1
  exact ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)

/-- The computed polynomial has the required difference and vanishes at zero. -/
theorem antidifference_sound [DecidableEq R] (p : R[X]) :
    (antidifference p).comp (1 + X) - antidifference p = p ∧
      (antidifference p).eval 0 = 0 := by
  rw [antidifference_eq_linear]
  exact ⟨antidifferenceLinear_step p, antidifferenceLinear_eval_zero p⟩

theorem antidifference_step [DecidableEq R] (p : R[X]) :
    (antidifference p).comp (1 + X) - antidifference p = p :=
  (antidifference_sound p).1

@[simp] theorem antidifference_eval_zero [DecidableEq R] (p : R[X]) :
    (antidifference p).eval 0 = 0 := (antidifference_sound p).2

theorem antidifference_natDegree_le [DecidableEq R] (p : R[X]) :
    (antidifference p).natDegree ≤ p.natDegree + 1 := by
  rw [antidifference_eq_linear]
  exact antidifferenceLinear_natDegree_le p

theorem antidifference_apply [DecidableEq R] (p : R[X]) :
    antidifference p =
      ∑ n ∈ p.support, p.coeff n • (monomialPrimitive n).map (algebraMap ℚ R) := by
  rw [antidifference_eq_linear, antidifferenceLinear_apply]

@[simp] theorem antidifference_monomial [DecidableEq R] (n : ℕ) (a : R) :
    antidifference (monomial n a) = a • (monomialPrimitive n).map (algebraMap ℚ R) := by
  rw [antidifference_eq_linear, antidifferenceLinear_monomial]

@[simp] theorem antidifference_C [DecidableEq R] (a : R) :
    antidifference (C a) = C a * X := by
  rw [antidifference_eq_linear, antidifferenceLinear_C]

/-- Specialization commutes with the computed polynomial, including when its
input degree drops. The algebra homomorphism need not be injective. -/
theorem antidifference_map [DecidableEq R] [DecidableEq S] (f : R →ₐ[ℚ] S) (p : R[X]) :
    (antidifference p).map f.toRingHom = antidifference (p.map f.toRingHom) := by
  simp only [antidifference_eq_linear, antidifferenceLinear_map]

theorem antidifference_eval_step [DecidableEq R] (p : R[X]) (x : R) :
    (antidifference p).eval (x + 1) - (antidifference p).eval x = p.eval x := by
  rw [antidifference_eq_linear]
  exact antidifferenceLinear_eval_step p x

/-- Evaluate the computed polynomial to obtain a finite sum. -/
theorem sum_range [DecidableEq R] (p : R[X]) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval (k : R) = (antidifference p).eval (n : R) := by
  rw [antidifference_eq_linear]
  exact sum_range_linear p n

theorem sum_Ico [DecidableEq R] (p : R[X]) (m n : ℕ) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, p.eval (k : R) =
      (antidifference p).eval (n : R) - (antidifference p).eval (m : R) := by
  rw [antidifference_eq_linear]
  exact sum_Ico_linear p m n hmn

/-- Finite sums after any parameter specialization of the computed polynomial. -/
theorem sum_range_map [DecidableEq R] (f : R →ₐ[ℚ] S) (p : R[X]) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval₂ f.toRingHom (k : S) =
      (antidifference p).eval₂ f.toRingHom (n : S) := by
  rw [antidifference_eq_linear]
  exact sum_range_map_linear f p n

theorem sum_range_parameters {ι : Type*} [DecidableEq ι]
    (p : (MvPolynomial ι ℚ)[X]) (σ : ι → S) (n : ℕ) :
    ∑ k ∈ Finset.range n, p.eval₂ (MvPolynomial.aeval σ).toRingHom (k : S) =
      (antidifference p).eval₂ (MvPolynomial.aeval σ).toRingHom (n : S) :=
  sum_range_map (MvPolynomial.aeval σ) p n

/-- Parameter coefficients may be arbitrary functions; only their values enter
the specialized finite sum. -/
theorem sum_range_apply {Θ : Type*} [DecidableEq (Θ → R)]
    (p : Polynomial (Θ → R)) (θ : Θ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        p.eval₂ (Pi.evalRingHom (fun _ : Θ => R) θ) (k : R) =
      (antidifference p).eval₂ (Pi.evalRingHom (fun _ : Θ => R) θ) (n : R) :=
  sum_range_map (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) p n

/-- End-to-end finite-sum correctness of the executable coefficient algorithm
under any rational-algebra specialization. The output is computed in `R` before
specialization, and no decidable equality on the coefficient rings is required. -/
theorem sum_range_antidifferenceCoefficients (f : R →ₐ[ℚ] S) {N : ℕ}
    (a : Fin N → R) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ i : Fin N, f (a i) * (k : S) ^ i.val =
      ∑ j : Fin (N + 1), f ((antidifferenceCoefficients a)[j.val]) * (n : S) ^ j.val := by
  classical
  have h := sum_range_map_linear f (Polynomial.ofFn N a) n
  rw [← ofFn_antidifferenceCoefficients] at h
  simpa only [ofFn_eq_sum_monomial, eval₂_finsetSum, eval₂_monomial,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

/-- Coefficients may be arbitrary functions of parameters. Evaluating the
computed coefficient functions at a parameter value gives the requested sum. -/
theorem sum_range_antidifferenceCoefficients_apply {Θ : Type*} {N : ℕ}
    (a : Fin N → Θ → R) (θ : Θ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ i : Fin N, a i θ * (k : R) ^ i.val =
      ∑ j : Fin (N + 1), (antidifferenceCoefficients a)[j.val] θ * (n : R) ^ j.val := by
  simpa only [Pi.evalAlgHom_apply] using sum_range_antidifferenceCoefficients
    (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) a n

/-- Specialization can also be performed directly on the executable coefficient vectors. -/
theorem antidifferenceCoefficients_map (f : R →ₐ[ℚ] S) {N : ℕ} (a : Fin N → R) :
    antidifferenceCoefficients (fun n => f (a n)) = (antidifferenceCoefficients a).map f := by
  apply Vector.ext
  intro k hk
  simp [antidifferenceCoefficients_get]

end

end Gosper.PolynomialSum
