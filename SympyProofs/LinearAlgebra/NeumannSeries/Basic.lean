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

open Filter Matrix Asymptotics
open scoped Topology Matrix

section NormedRing

variable {R : Type*} [NormedRing R]

/-- Powers that tend to zero decay fast enough to absorb any weights `u k` of polynomial growth. -/
theorem summable_norm_mul_pow_of_tendsto_zero {a : R}
    (h : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0)) {p : ℕ} {u : ℕ → ℕ}
    (hu : (fun k : ℕ => (u k : ℝ)) =O[atTop] fun k : ℕ => ((k ^ p : ℕ) : ℝ)) :
    Summable (fun k : ℕ => ‖(u k : R) * a ^ k‖) := by
  obtain ⟨N, hN⟩ := ((h.norm.eventually (gt_mem_nhds (by simp : ‖(0 : R)‖ < 1))).and
    (eventually_gt_atTop 0)).exists
  have hnorm : ‖a ^ N‖ < 1 := by simpa using hN.1
  have : NeZero N := ⟨Nat.ne_of_gt hN.2⟩
  have hs (j : Fin N) :
      Summable (fun q : ℕ => ‖(u (q * N + j.val) : R) * a ^ (q * N + j.val)‖) := by
    have hshift : Tendsto (fun q : ℕ => q * N + j.val) atTop atTop :=
      tendsto_atTop_mono (fun q => (Nat.le_mul_of_pos_right q hN.2).trans (Nat.le_add_right _ _))
        tendsto_id
    have hu' : (fun q : ℕ => (u (q * N + j.val) : ℝ)) =O[atTop]
        fun q : ℕ => ((q ^ p : ℕ) : ℝ) := by
      refine (hu.comp_tendsto hshift).trans (IsBigO.of_bound ((2 * N : ℕ) ^ p : ℕ) ?_)
      filter_upwards [eventually_ge_atTop 1] with q hq
      simp only [Function.comp_apply, Real.norm_natCast]
      norm_cast
      calc (q * N + j.val) ^ p ≤ (2 * N * q) ^ p := by
            gcongr
            nlinarith [j.isLt]
        _ = (2 * N) ^ p * q ^ p := Nat.mul_pow _ _ _
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      ((summable_norm_mul_geometric_of_norm_lt_one hnorm hu').mul_right ‖a ^ j.val‖)
    simpa only [pow_add, pow_mul, Nat.mul_comm, mul_assoc] using
      norm_mul_le ((u (q * N + j.val) : R) * (a ^ N) ^ q) (a ^ j.val)
  have hp : Summable (fun x : ℕ × Fin N =>
      ‖(u (x.1 * N + x.2.val) : R) * a ^ (x.1 * N + x.2.val)‖) :=
    ((summable_prod_of_nonneg (f := fun x : Fin N × ℕ =>
      ‖(u (x.2 * N + x.1.val) : R) * a ^ (x.2 * N + x.1.val)‖) (fun _ => norm_nonneg _)).mpr
      ⟨hs, (hasSum_fintype _).summable⟩).prod_symm
  exact (Nat.divModEquiv N).symm.summable_iff.mp hp

end NormedRing

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The polynomially weighted series `∑ k ^ p * A ^ k` converges exactly when `A ^ k → 0`. -/
theorem summable_pow_mul_pow_iff_tendsto_zero (p : ℕ) (A : Matrix n n 𝕜) :
    Summable (fun k : ℕ => (k : Matrix n n 𝕜) ^ p * A ^ k) ↔
      Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  open scoped Matrix.Norms.Operator in
  simp only [← Nat.cast_pow]
  constructor
  · intro h
    refine squeeze_zero_norm' ?_ (tendsto_zero_iff_norm_tendsto_zero.mp h.tendsto_atTop_zero)
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [Real.norm_natCast]
    exact_mod_cast Nat.one_le_pow _ _ hk
  · exact fun h => .of_norm (summable_norm_mul_pow_of_tendsto_zero h (isBigO_refl _ _))

theorem summable_pow_iff_tendsto_zero (A : Matrix n n 𝕜) :
    Summable (fun k : ℕ => A ^ k) ↔ Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  simpa using summable_pow_mul_pow_iff_tendsto_zero 0 A

/-- Polynomial weights do not change the convergence condition of the matrix geometric series. -/
theorem summable_pow_mul_pow_iff_summable_pow (p : ℕ) (A : Matrix n n 𝕜) :
    Summable (fun k : ℕ => (k : Matrix n n 𝕜) ^ p * A ^ k) ↔ Summable (fun k : ℕ => A ^ k) :=
  (summable_pow_mul_pow_iff_tendsto_zero p A).trans (summable_pow_iff_tendsto_zero A).symm

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
