import SympyProofs.RiemannZeta.RightHalfPlane
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # A paired series converging to the left of the original boundary

Pairing adjacent terms of the alternating Dirichlet series gives an absolutely
convergent sum on `0 < re s`. The estimates below also give local holomorphy.
No continued zeta function is imported.
-/

noncomputable section
namespace RiemannZeta

open Set Filter
open scoped Topology

def pairedTerm (n : ℕ) (s : ℂ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

def eta (s : ℂ) : ℂ := ∑' n, pairedTerm n s

/-- A uniform bound obtained by integrating, or applying the mean value bound to,
the derivative of `x ↦ x⁻ˢ` across one unit interval. -/
theorem norm_pairedTerm_le {s : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : σ ≤ s.re) (n : ℕ) :
    ‖pairedTerm n s‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-σ - 1) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  let a : ℝ := 2 * n + 1
  let b : ℝ := 2 * n + 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) (Icc a b) x :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le hx.1))
      (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hb (x : ℝ) (hx : x ∈ Ico a b) :
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-σ - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hx1 : 1 ≤ x := by dsimp [a] at hx; have := Nat.cast_nonneg (α := ℝ) n; linarith [hx.1]
    calc
      x ^ (-s - 1).re ≤ x ^ (-σ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by simp; linarith)
      _ ≤ ((n : ℝ) + 1) ^ (-σ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by dsimp [a] at hx; have := Nat.cast_nonneg (α := ℝ) n; linarith [hx.1])
          (by linarith)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb b ⟨hab, le_rfl⟩
  norm_num [pairedTerm, a, b, norm_sub_rev] at h ⊢
  exact h

theorem summable_pairedTerm {s : ℂ} (hs : 0 < s.re) : Summable (fun n => pairedTerm n s) := by
  have hpow : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re - 1)) := by
    have h := (Real.summable_nat_rpow.mpr (by linarith : -s.re - 1 < -1))
    simpa using (summable_nat_add_iff 1).mpr h
  exact (hpow.mul_left ‖s‖).of_norm_bounded (fun n => norm_pairedTerm_le hs le_rfl n)

theorem differentiable_pairedTerm (n : ℕ) : Differentiable ℂ (pairedTerm n) := by
  intro s
  exact ((differentiableAt_id.neg).const_cpow (Or.inl (by norm_cast))).sub
    ((differentiableAt_id.neg).const_cpow (Or.inl (by norm_cast)))

theorem differentiableAt_eta {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ eta s := by
  let σ := s.re / 2
  let M := ‖s‖ + 1
  let U : Set ℂ := {z | σ < z.re ∧ ‖z‖ < M}
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by dsimp [U, σ, M]; constructor <;> linarith
  have hpow : Summable (fun n : ℕ => M * ((n : ℝ) + 1) ^ (-σ - 1)) := by
    apply Summable.mul_left
    have h := Real.summable_nat_rpow.mpr (by linarith : -σ - 1 < -1)
    simpa using (summable_nat_add_iff 1).mpr h
  have hd : DifferentiableOn ℂ eta U :=
    Complex.differentiableOn_tsum_of_summable_norm hpow
      (fun n => (differentiable_pairedTerm n).differentiableOn) hU
      (fun n z hz => (norm_pairedTerm_le hσ hz.1.le n).trans
        (mul_le_mul_of_nonneg_right hz.2.le (Real.rpow_nonneg (by positivity) _)))
  exact hd.differentiableAt (hU.mem_nhds hsU)

theorem analyticOnNhd_eta : AnalyticOnNhd ℂ eta {s | 0 < s.re} :=
  (show DifferentiableOn ℂ eta {s | 0 < s.re} from
    fun _ hs => (differentiableAt_eta hs).differentiableWithinAt).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)

/-- In the original half-plane, rearranging an absolutely convergent sum gives
the alternating-series identity. -/
theorem eta_eq_factor_mul_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    eta s = (1 - (2 : ℂ) ^ (1 - s)) * series s := by
  let f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s)
  have hf : Summable f := by
    simpa [f, Complex.cpow_neg, one_div] using (summable_iff s).mpr hs
  have he : Summable (fun n => f (2 * n)) :=
    hf.comp_injective (by intro n m h; change 2 * n = 2 * m at h; omega)
  have ho : Summable (fun n => f (2 * n + 1)) :=
    hf.comp_injective (by intro n m h; change 2 * n + 1 = 2 * m + 1 at h; omega)
  have hsplit := tsum_even_add_odd he ho
  have htotal : (∑' n, f n) = series s := by simp [f, series, Complex.cpow_neg, one_div]
  have heven : (∑' n, f (2 * n + 1)) = (2 : ℂ) ^ (-s) * series s := by
    have hterm (n : ℕ) : f (2 * n + 1) = (2 : ℂ) ^ (-s) * f n := by
      dsimp [f]
      have hbase : ((2 * n + 1 : ℕ) : ℂ) + 1 = (2 : ℂ) * ((n + 1 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hbase]
      simpa using Complex.natCast_mul_natCast_cpow 2 (n + 1) (-s)
    simp_rw [hterm]
    rw [tsum_mul_left, htotal]
  have heta : eta s = (∑' n, f (2 * n)) - ∑' n, f (2 * n + 1) := by
    rw [← he.tsum_sub ho]
    apply tsum_congr
    intro n
    norm_num [pairedTerm, f, Nat.cast_add, Nat.cast_mul, add_assoc]
  rw [htotal, heven] at hsplit
  have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [heta, heven, hpow]
  linear_combination hsplit

end RiemannZeta
