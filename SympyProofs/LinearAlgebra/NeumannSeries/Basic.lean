module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Matrix geometric series and decay of matrix powers. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Filter Matrix
open scoped Topology Matrix

section NormedRing

variable {R : Type*} [NormedRing R] [CompleteSpace R]

theorem summable_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) :
    Summable (fun k : ℕ => a ^ k) := by
  obtain ⟨N, hN⟩ := ((h.norm.eventually (gt_mem_nhds (by simp : ‖(0 : R)‖ < 1))).and
    (eventually_gt_atTop 0)).exists
  have hnorm : ‖a ^ N‖ < 1 := by simpa using hN.1
  have : NeZero N := ⟨Nat.ne_of_gt hN.2⟩
  have hs (j : Fin N) : Summable (fun k : ℕ => ‖a ^ (k * N + j.val)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => ?_) ((summable_norm_geometric_of_norm_lt_one hnorm).mul_right ‖a ^ j.val‖)
    simpa only [pow_add, pow_mul, Nat.mul_comm] using norm_mul_le ((a ^ N) ^ k) (a ^ j.val)
  have hp : Summable (fun p : ℕ × Fin N => a ^ (p.1 * N + p.2.val)) := by
    apply Summable.of_norm
    exact ((summable_prod_of_nonneg (f := fun p : Fin N × ℕ =>
      ‖a ^ (p.2 * N + p.1.val)‖) (fun _ => norm_nonneg _)).mpr
      ⟨hs, (hasSum_fintype _).summable⟩).prod_symm
  exact (Nat.divModEquiv N).symm.summable_iff.mp hp

end NormedRing

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

theorem summable_pow_iff_tendsto_zero (A : Matrix n n 𝕜) :
    Summable (fun k : ℕ => A ^ k) ↔ Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  constructor
  · exact Summable.tendsto_atTop_zero
  · open scoped Matrix.Norms.Operator in
      exact summable_pow_of_tendsto_zero

/-- For matrix geometric series, summability agrees with convergence of ordinary partial sums. -/
theorem summable_pow_iff_tendsto_sum (A : Matrix n n 𝕜) :
    Summable (fun k : ℕ => A ^ k) ↔
      ∃ S, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, A ^ k) atTop (𝓝 S) := by
  constructor
  · intro h
    exact ⟨_, h.hasSum.tendsto_sum_nat⟩
  · rintro ⟨S, hS⟩
    apply (summable_pow_iff_tendsto_zero A).mpr
    have ht := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
    simpa [Function.comp_def, Finset.sum_range_succ] using ht

theorem hasSum_inverse {A : Matrix n n 𝕜} (h : Summable (fun k : ℕ => A ^ k)) :
    HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  have he := h.one_sub_mul_tsum_pow
  have hu : IsUnit (1 - A) := isUnit_iff_exists_inv.mpr ⟨_, he⟩
  convert h.hasSum using 1
  exact hu.mul_right_injective (by
    dsimp
    rw [he, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)])

end SympyProofs.NeumannSeries
