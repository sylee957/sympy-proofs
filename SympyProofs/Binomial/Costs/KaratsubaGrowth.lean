module

public import SympyProofs.Binomial.Costs.FactorBounds
public import SympyProofs.Python.Cost.Karatsuba.Work
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Growth estimates used by the Karatsuba runtime proof

Chebyshev's upper bound, rather than the prime number theorem, suffices: the
number of factors times their maximum bit width is `O(n)`. The remaining
sieve and small-integer work grow strictly slower than the Karatsuba envelope.
-/

@[expose] public section
open Filter Asymptotics Python.Cost.Karatsuba
namespace SympyBinomial.PrimeExponent

theorem inputWidth_le_log (n : ℕ) (hn : 2 ≤ n) :
    (inputWidth n:ℝ) ≤ (2 / Real.log 2) * Real.log n := by
  have h2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2:ℝ)^Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^Nat.log 2 n) hpow
  rw [Real.log_pow] at hlog
  have hbase := Real.log_le_log (by norm_num : (0:ℝ) < 2) hnR
  apply (mul_le_mul_iff_of_pos_right h2).mp
  rw [inputWidth_eq, Nat.log2_eq_log_two, Nat.cast_add, Nat.cast_one]
  have he : ((2 / Real.log 2) * Real.log n) * Real.log 2 = 2*Real.log n := by
    field_simp
  rw [he]
  nlinarith only [hlog,hbase]

/-- Chebyshev's estimate cancels the logarithm from the per-factor width. -/
theorem primeCount_width_isBigO :
    (fun n : ℕ => (((n.primeCounting+1)*inputWidth n:ℕ):ℝ)) =O[atTop]
      (fun n => (n:ℝ)) := by
  let c := 2 / Real.log (2:ℝ)
  let a := Real.log (4:ℝ)+1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha : 0 ≤ a+1 := by dsimp [a]; positivity
  apply IsBigO.of_bound (c*(a+1))
  have hp := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  filter_upwards [hp, eventually_ge_atTop 2] with n hp hn
  simp only [Nat.floor_natCast] at hp
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hp' : (n.primeCounting:ℝ)*Real.log n ≤ a*n := (le_div_iff₀ hlog).mp hp
  have hw := inputWidth_le_log n hn
  have hln := Real.log_le_self hn0.le
  simp only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (((n.primeCounting+1)*inputWidth n:ℕ):ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg _)]
  calc
    (((n.primeCounting+1)*inputWidth n:ℕ):ℝ) =
        ((n.primeCounting:ℝ)+1)*(inputWidth n:ℝ) := by push_cast; rfl
    _ ≤ ((n.primeCounting:ℝ)+1)*(c*Real.log n) := by gcongr
    _ = c*((n.primeCounting:ℝ)*Real.log n+Real.log n) := by ring
    _ ≤ c*(a*n+n) := mul_le_mul_of_nonneg_left (add_le_add hp' hln) hc
    _ = c*(a+1)*n := by ring

/-- The padded tree envelope keeps the Karatsuba exponent after accounting for
both the number and the maximum width of the prime-power factors. -/
theorem primeTree_work_isBigO :
    (fun n : ℕ => ((work (n.primeCounting+1)*work (inputWidth n):ℕ):ℝ)) =O[atTop]
      (fun n => (n:ℝ)^exponent) := by
  have hp := primeCount_width_isBigO.rpow exponent_pos.le
    (show 0 ≤ᶠ[atTop] (fun n : ℕ => (n:ℝ)) from Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
  apply IsBigO.trans (g := fun n : ℕ => ((((n.primeCounting+1)*inputWidth n:ℕ):ℝ)^exponent)) ?_ hp
  apply IsBigO.of_bound 9
  filter_upwards [] with n
  have hleft := work_le_rpow (n.primeCounting+1) (by omega)
  have hright := work_le_rpow (inputWidth n) (inputWidth_pos n)
  have h := mul_le_mul hleft hright (Nat.cast_nonneg _) (by positivity)
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ ((work (n.primeCounting+1)*work (inputWidth n):ℕ):ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (show (0:ℝ) ≤ (((n.primeCounting+1)*inputWidth n:ℕ):ℝ) from Nat.cast_nonneg _) exponent)]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  push_cast at h
  nlinarith only [h]

/-- Cubic arithmetic on input-sized words, repeated at most linearly many times. -/
theorem wordWork_isBigO :
    (fun n : ℕ => (((n+1)*inputWidth n^3:ℕ):ℝ)) =O[atTop]
      (fun n => (n:ℝ)^exponent) := by
  let c := 2 / Real.log (2:ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hw : (fun n : ℕ => (((n+1)*inputWidth n^3:ℕ):ℝ)) =O[atTop]
      (fun n => (n:ℝ)*Real.log n^3) := by
    apply IsBigO.of_bound (2*c^3)
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
    have hW := inputWidth_le_log n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)*Real.log n^3)]
    push_cast
    calc
      ((n:ℝ)+1)*(inputWidth n:ℝ)^3 ≤ (2*n)*(c*Real.log n)^3 := by gcongr; linarith
      _ = (2*c^3)*((n:ℝ)*Real.log n^3) := by ring
  have hlog : (fun n : ℕ => Real.log (n:ℝ)^3) =O[atTop]
      (fun n => (n:ℝ)^(exponent-1)) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using
      ((isLittleO_log_rpow_rpow_atTop (3:ℝ) (sub_pos.mpr one_lt_exponent)).isBigO.comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := (isBigO_refl (fun n : ℕ => (n:ℝ)) atTop).mul hlog
  apply hw.trans
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (n:ℝ)*(n:ℝ)^(exponent-1) = (n:ℝ)^(1+(exponent-1)) := by
      rw [Real.rpow_add hn0,Real.rpow_one]
    _ = (n:ℝ)^exponent := by congr 1; ring

/-- Even the coarse marking budget is `O(n^(3/2))`, hence below the Karatsuba exponent. -/
theorem sieveWork_isBigO :
    (fun n : ℕ => (((n.sqrt+1)*(n+1+inputWidth n^2):ℕ):ℝ)) =O[atTop]
      (fun n => (n:ℝ)^exponent) := by
  apply IsBigO.of_bound 36
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hw : inputWidth n^2 ≤ 8*(n+1) :=
    (Nat.pow_le_pow_right (inputWidth_pos n) (by omega : 2 ≤ 3)).trans (inputWidth_cube_le n)
  have hwR : (inputWidth n:ℝ)^2 ≤ 8*((n:ℝ)+1) := by exact_mod_cast hw
  have hs : (n.sqrt:ℝ) ≤ Real.sqrt n :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hpow : (n:ℝ)^(3/2:ℝ) ≤ (n:ℝ)^exponent :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) three_halves_lt_exponent.le
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0.le exponent)]
  push_cast
  calc
    ((n.sqrt:ℝ)+1)*((n:ℝ)+1+(inputWidth n:ℝ)^2) ≤
        (2*Real.sqrt n)*(18*n) := by gcongr <;> linarith
    _ = 36*((n:ℝ)^(3/2:ℝ)) := by
      rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1/2+1 by norm_num,
        Real.rpow_add hn0,Real.rpow_one]
      ring
    _ ≤ 36*(n:ℝ)^exponent := by gcongr

end SympyBinomial.PrimeExponent
