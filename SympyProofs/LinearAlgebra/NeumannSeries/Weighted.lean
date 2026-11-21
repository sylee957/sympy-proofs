module

public import SympyProofs.LinearAlgebra.NeumannSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling

/-! Closed forms of polynomially weighted matrix geometric series. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Filter Matrix Asymptotics Finset Nat
open scoped Topology Matrix Ring

section NormedRing

variable {R : Type*} [NormedRing R]

theorem summable_norm_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) : Summable (fun k : ℕ => ‖a ^ k‖) := by
  simpa using summable_norm_mul_pow_of_tendsto_zero h (u := fun _ => 1) (p := 0)
    (by simpa using isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop)

variable [CompleteSpace R]

/-- The geometric series of an element whose powers tend to zero sums to `(1 - a)⁻¹ʳ`. -/
theorem hasSum_pow_ringInverse_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) :
    HasSum (fun k : ℕ => a ^ k) (1 - a)⁻¹ʳ := by
  have hs : Summable (fun k : ℕ => a ^ k) := .of_norm (summable_norm_pow_of_tendsto_zero h)
  let u : Rˣ := ⟨1 - a, ∑' k : ℕ, a ^ k, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  have hu : (1 - a)⁻¹ʳ = ∑' k : ℕ, a ^ k := Ring.inverse_unit u
  rw [hu]
  exact hs.hasSum

/-- `∑ (k + j).choose j * a ^ k = (1 - a)⁻¹ʳ ^ (j + 1)` whenever the powers of `a` tend to zero.

This is `hasSum_choose_mul_geometric_of_norm_lt_one'` with `‖a‖ < 1` weakened to `a ^ k → 0`. -/
theorem hasSum_choose_mul_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) (j : ℕ) :
    HasSum (fun k : ℕ => ((k + j).choose j : R) * a ^ k) ((1 - a)⁻¹ʳ ^ (j + 1)) := by
  have hgeom := hasSum_pow_ringInverse_of_tendsto_zero h
  induction j with
  | zero => simpa using hgeom
  | succ j ih =>
      have I1 : Summable (fun k : ℕ => ‖((k + j).choose j : R) * a ^ k‖) := by
        apply summable_norm_mul_pow_of_tendsto_zero (p := j) h
        apply isBigO_iff.2 ⟨2 ^ j, ?_⟩
        filter_upwards [Ioi_mem_atTop j] with k (hk : j < k)
        simp only [Real.norm_eq_abs, abs_cast, cast_pow, norm_pow]
        norm_cast
        calc (k + j).choose j
          _ ≤ (2 * k).choose j := choose_le_choose j (by lia)
          _ ≤ (2 * k) ^ j := Nat.choose_le_pow _ _
          _ = 2 ^ j * k ^ j := Nat.mul_pow 2 k j
      convert!
        hasSum_sum_range_mul_of_summable_norm' I1 ih.summable
          (summable_norm_pow_of_tendsto_zero h) hgeom.summable with
        k
      · have : ∑ i ∈ Finset.range (k + 1), ↑((i + j).choose j) * a ^ i * a ^ (k - i) =
            ∑ i ∈ Finset.range (k + 1), ↑((i + j).choose j) * a ^ k := by
          apply Finset.sum_congr rfl (fun i hi ↦ ?_)
          simp only [Finset.mem_range] at hi
          rw [mul_assoc, ← pow_add, show i + (k - i) = k by lia]
        simp [this, ← sum_mul, ← Nat.cast_sum, sum_range_add_choose k j, add_assoc]
      · rw [ih.tsum_eq, hgeom.tsum_eq, pow_succ]

theorem hasSum_descFactorial_mul_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) (j : ℕ) :
    HasSum (fun k : ℕ => (k.descFactorial j : R) * a ^ k)
      (j.factorial * a ^ j * (1 - a)⁻¹ʳ ^ (j + 1)) := by
  rw [← hasSum_nat_add_iff' j]
  convert (hasSum_choose_mul_pow_of_tendsto_zero h j).mul_left (j.factorial * a ^ j) using 1
  · funext k
    symm
    push_cast [Nat.descFactorial_eq_factorial_mul_choose]
    rw [mul_assoc, (Nat.cast_commute ((k + j).choose j) (a ^ j)).symm.left_comm, ← pow_add,
      add_comm j k, mul_assoc]
  · exact sub_eq_self.2 <| Finset.sum_eq_zero fun i hi ↦ by
      simp [descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hi)]

/-- `∑ k ^ p * a ^ k` in closed form, with `S(p, j)` the Stirling numbers of the second kind.

This is `hasSum_pow_mul_geometric_of_norm_lt_one'` with `‖a‖ < 1` weakened to `a ^ k → 0`. -/
theorem hasSum_pow_mul_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) (p : ℕ) :
    HasSum (fun k : ℕ => (k : R) ^ p * a ^ k)
      (∑ j ∈ Finset.range (p + 1),
        stirlingSecond p j * j.factorial * a ^ j * (1 - a)⁻¹ʳ ^ (j + 1)) := by
  simpa only [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Nat.cast_sum,
    Nat.cast_mul, Finset.sum_mul, mul_assoc] using
    hasSum_sum fun j _ ↦ (hasSum_descFactorial_mul_pow_of_tendsto_zero h j).mul_left _

end NormedRing

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- `∑ (k + j).choose j * A ^ k = (1 - A)⁻¹ ^ (j + 1)` for a convergent matrix geometric series. -/
theorem hasSum_choose_mul_pow {A : Matrix n n 𝕜} (h : Summable (fun k : ℕ => A ^ k)) (j : ℕ) :
    HasSum (fun k : ℕ => ((k + j).choose j : Matrix n n 𝕜) * A ^ k) ((1 - A)⁻¹ ^ (j + 1)) := by
  open scoped Matrix.Norms.Operator in
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact hasSum_choose_mul_pow_of_tendsto_zero h.tendsto_atTop_zero j

/-- The polynomially weighted matrix series `∑ k ^ p * A ^ k` in closed form, with `S(p, j)` the
Stirling numbers of the second kind. -/
theorem hasSum_pow_mul_pow {A : Matrix n n 𝕜} (h : Summable (fun k : ℕ => A ^ k)) (p : ℕ) :
    HasSum (fun k : ℕ => (k : Matrix n n 𝕜) ^ p * A ^ k)
      (∑ j ∈ Finset.range (p + 1),
        stirlingSecond p j * j.factorial * A ^ j * (1 - A)⁻¹ ^ (j + 1)) := by
  open scoped Matrix.Norms.Operator in
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact hasSum_pow_mul_pow_of_tendsto_zero h.tendsto_atTop_zero p

/-- `∑ k * A ^ k = A * (1 - A)⁻¹ ^ 2` for a convergent matrix geometric series. -/
theorem hasSum_natCast_mul_pow {A : Matrix n n 𝕜} (h : Summable (fun k : ℕ => A ^ k)) :
    HasSum (fun k : ℕ => (k : Matrix n n 𝕜) * A ^ k) (A * (1 - A)⁻¹ ^ 2) := by
  simpa [sum_range_succ, stirlingSecond_self] using hasSum_pow_mul_pow h 1

/-- `∑ k ^ 2 * A ^ k = A * (1 + A) * (1 - A)⁻¹ ^ 3` for a convergent matrix geometric series. -/
theorem hasSum_sq_mul_pow {A : Matrix n n 𝕜} (h : Summable (fun k : ℕ => A ^ k)) :
    HasSum (fun k : ℕ => (k : Matrix n n 𝕜) ^ 2 * A ^ k) (A * (1 + A) * (1 - A)⁻¹ ^ 3) := by
  have hu : (1 - A) * (1 - A)⁻¹ = 1 := by
    simpa [(hasSum_inverse h).tsum_eq] using h.one_sub_mul_tsum_pow
  have h1 : (1 - A)⁻¹ ^ 2 = (1 - A) * (1 - A)⁻¹ ^ 3 := by
    rw [pow_succ' _ 2, ← mul_assoc, hu, one_mul]
  have h2 : A * (1 + A) * (1 - A)⁻¹ ^ 3 = A * (1 - A)⁻¹ ^ 2 + 2 * A ^ 2 * (1 - A)⁻¹ ^ 3 := by
    rw [h1]
    noncomm_ring
  rw [h2]
  simpa [Finset.sum_range_succ, stirlingSecond_one_right, stirlingSecond_self] using
    hasSum_pow_mul_pow h 2

end SympyProofs.NeumannSeries
