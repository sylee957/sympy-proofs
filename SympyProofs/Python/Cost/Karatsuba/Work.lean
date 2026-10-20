module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Tactic

/-!
# A dyadic Karatsuba work envelope

Padding a width to `2^d` gives a `3^d` multiplication budget. The lemmas below
identify its exponent and make the rounding cost explicit. This is an arithmetic
cost envelope, not a verification of a machine multiplication implementation.
-/

@[expose] public section
namespace Python.Cost.Karatsuba

noncomputable def exponent : ℝ := Real.log 3 / Real.log 2

def work (bits : ℕ) : ℕ := 3 ^ Nat.clog 2 bits

theorem exponent_pos : 0 < exponent := by
  unfold exponent
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem one_lt_exponent : 1 < exponent := by
  unfold exponent
  rw [lt_div_iff₀ (Real.log_pos (by norm_num))]
  simpa using Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)

theorem three_halves_lt_exponent : (3:ℝ)/2 < exponent := by
  unfold exponent
  rw [lt_div_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 2^3)
    (by norm_num : (2:ℝ)^3 < 3^2)
  simp only [Real.log_pow, Nat.cast_ofNat] at h
  linarith

theorem exponent_lt_two : exponent < 2 := by
  unfold exponent
  rw [div_lt_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) < 2^2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem two_rpow_exponent : (2:ℝ) ^ exponent = 3 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  unfold exponent
  rw [mul_div_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2)))]
  exact Real.exp_log (by norm_num)

theorem dyadic_rpow (d : ℕ) : ((2:ℝ)^d)^exponent = (3:ℝ)^d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast, two_rpow_exponent]

theorem work_pos (bits : ℕ) : 0 < work bits := by unfold work; positivity

theorem bits_le_work (bits : ℕ) : bits ≤ work bits :=
  (Nat.le_pow_clog (by omega) bits).trans (Nat.pow_le_pow_left (by omega) _)

theorem work_mono : Monotone work := fun _ _ h =>
  Nat.pow_le_pow_right (by omega) (Nat.clog_mono_right 2 h)

theorem work_mul_le (a b : ℕ) : work (a*b) ≤ work a * work b := by
  unfold work
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by omega) a) (Nat.le_pow_clog (by omega) b)

@[simp] theorem work_two_pow (d : ℕ) : work (2^d) = 3^d := by
  simp [work, Nat.clog_pow]

theorem rpow_le_work (bits : ℕ) : (bits:ℝ)^exponent ≤ work bits := by
  have h := Nat.le_pow_clog (by omega : 1 < 2) bits
  have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ bits)
    (show (bits:ℝ) ≤ (2:ℝ)^Nat.clog 2 bits by exact_mod_cast h) exponent_pos.le
  simpa only [dyadic_rpow, work, Nat.cast_pow, Nat.cast_ofNat] using hr

theorem work_le_rpow (bits : ℕ) (hbits : 0 < bits) :
    (work bits : ℝ) ≤ 3 * (bits:ℝ)^exponent := by
  by_cases h : bits ≤ 1
  · have hb : bits = 1 := by omega
    simp [hb, work]
  · let d := Nat.clog 2 bits
    have hd : 0 < d := by
      have := (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2) (x := bits) (y := 0))
      simp only [pow_zero] at this
      exact this.mpr (by omega)
    have hpow : 2^(d-1) < bits := Nat.pow_pred_clog_lt_self (by omega) (by omega)
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^(d-1))
      (show (2:ℝ)^(d-1) ≤ bits by exact_mod_cast hpow.le) exponent_pos.le
    rw [dyadic_rpow] at hr
    calc
      (work bits : ℝ) = (3:ℝ)^d := by simp [work, d]
      _ = 3 * (3:ℝ)^(d-1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 3 * (bits:ℝ)^exponent := by gcongr

/-- The dyadic envelope has exactly the Karatsuba exponent, despite integer rounding. -/
theorem work_isTheta :
    (fun n : ℕ => (work (n+1) : ℝ)) =Θ[Filter.atTop]
      (fun n => ((n+1:ℕ):ℝ)^exponent) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 3
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (work (n+1):ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n+1)) exponent)] using
      work_le_rpow (n+1) (by omega)
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (show (0:ℝ) ≤ (work (n+1):ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n+1)) exponent)] using rpow_le_work (n+1)

end Python.Cost.Karatsuba
