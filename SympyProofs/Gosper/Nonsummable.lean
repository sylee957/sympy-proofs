module

public import SympyProofs.Gosper.Hypergeometric

/-! # The nonsummable example (3d) -/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The input ratio in (3d) already satisfies condition (6). -/
theorem example_3d_shiftCoprime : ShiftCoprime ((X - 1) ^ 3 : K[X]) ((X + 1) ^ 3 + 1) := by
  intro j
  apply IsCoprime.pow_left
  apply (irreducible_X_sub_C (1 : K)).coprime_iff_not_dvd.mpr
  rw [dvd_iff_isRoot]
  change (taylor (j : K) ((X + 1) ^ 3 + 1)).eval 1 ≠ 0
  simp only [taylor_eval, eval_add, eval_pow, eval_X, eval_one]
  have hn : (((j + 2) ^ 3 + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  convert hn using 1
  push_cast
  ring

private theorem example_3d_degree (f : K[X])
    (h : X ^ 3 * f - ((X + 1) ^ 3 + 1) * taylor (-1) f = 1) : f.natDegree ≤ 3 := by
  by_contra hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show f.natDegree ≠ 0 by omega)
  change f.natDegree = k + 1 at hk
  have hf : f ≠ 0 := by intro hz; simp [hz] at hn
  have he := degree_case_two_exception (1 : K[X]) (X ^ 3) ((X + 1) ^ 3 + 1) f 2 k
    (by compute_degree) (by compute_degree) hk hf
    (by norm_num [coeff_add, add_pow, coeff_one]) h (by simp)
  norm_num [coeff_add, add_pow, coeff_one] at he
  have hk2 : k = 2 := by exact_mod_cast (show (k : K) = 2 by linear_combination he)
  omega

/-- No polynomial certificate exists for (3d). -/
theorem example_3d_no_polynomial :
    ¬∃ f : K[X], operator ((X - 1) ^ 3) ((X + 1) ^ 3 + 1) f = 1 := by
  rintro ⟨f, he⟩
  have hs : taylor (1 : K) ((X - 1) ^ 3) = X ^ 3 := by
    simp [taylor_pow, map_sub, taylor_X]
  rw [operator_apply, hs] at he
  have hd := example_3d_degree f he
  have hf := f.as_sum_range_C_mul_X_pow' (show f.natDegree < 4 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hf
  rw [hf] at he
  simp only [map_add, taylor_mul, taylor_C, taylor_X_pow] at he
  have h0 := congrArg (fun p : K[X] => p.eval 0) he
  have h1 := congrArg (fun p : K[X] => p.eval 1) he
  have h2 := congrArg (fun p : K[X] => p.eval 2) he
  have h3 := congrArg (fun p : K[X] => p.eval 3) he
  have h4 := congrArg (fun p : K[X] => p.eval 4) he
  norm_num [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow] at h0 h1 h2 h3 h4
  have h01 : (0 : K) = 1 := by
    linear_combination 7 * h0 - (40 / 3 : K) * h1 + (35 / 3 : K) * h2 - (16 / 3 : K) * h3 + h4
  exact zero_ne_one h01

/-- The rational-function obstruction asserted in (3d). -/
theorem example_3d_no_rational :
    ¬∃ f : RatFunc K, RationalSolution 1 ((X - 1) ^ 3) ((X + 1) ^ 3 + 1) f := by
  rw [rational_solution_iff_polynomial _ _ _ example_3d_shiftCoprime]
  exact example_3d_no_polynomial

/-- Hence no rational multiplier supplies an indefinite sum for the term
ratio `(n-1)^3 / ((n+1)^3+1)`. -/
theorem example_3d_not_summable :
    ¬HasRationalAntidifference (normalRatio (1 : K[X]) ((X - 1) ^ 3) ((X + 1) ^ 3 + 1)) := by
  rw [summable_iff_rational_solution (1 : K[X]) ((X - 1) ^ 3) ((X + 1) ^ 3 + 1) one_ne_zero
    (by simpa using pow_ne_zero 3 (X_sub_C_ne_zero (1 : K))) (by
      intro h
      have := congrArg (fun p : K[X] => p.eval 0) h
      norm_num at this)]
  exact example_3d_no_rational

/-- The full nonsummability assertion in (3d), using the paper's sum-ratio criterion. -/
theorem example_3d_no_hypergeometric_sum :
    ¬HasHypergeometricAntidifference
      (normalRatio (1 : K[X]) ((X - 1) ^ 3) ((X + 1) ^ 3 + 1)) := by
  intro h
  apply example_3d_not_summable (K := K)
  apply (hypergeometric_iff_rational _ ?_).mp h
  unfold normalRatio
  apply div_ne_zero
  · intro h
    have he := (IsFractionRing.injective K[X] (RatFunc K))
      (h.trans (map_zero (algebraMap K[X] (RatFunc K))).symm)
    have hn : ((X - 1) ^ 3 : K[X]) ≠ 0 := by
      simpa using pow_ne_zero 3 (X_sub_C_ne_zero (1 : K))
    exact hn (by simpa only [one_mul] using he)
  · intro h
    have he := (IsFractionRing.injective K[X] (RatFunc K))
      (h.trans (map_zero (algebraMap K[X] (RatFunc K))).symm)
    simp only [taylor_one, Polynomial.C_1, one_mul] at he
    have := congrArg (fun p : K[X] => p.eval 0) he
    norm_num at this

end Gosper
