module

public import SympyProofs.LinearAlgebra.NeumannSeries.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.Order.Star.Real

/-! The discrete Lyapunov equation characterizes summability of matrix powers. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Filter Matrix
open scoped Topology Matrix

variable {n : Type*} [Fintype n]

def energy (P : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

def stein (A P : Matrix n n ℝ) : Matrix n n ℝ := P - Aᵀ * P * A

lemma energy_conjugate (A P : Matrix n n ℝ) (x : n → ℝ) :
    energy (Aᵀ * P * A) x = energy P (A *ᵥ x) := by
  simp only [energy, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, vecMul_vecMul]

lemma energy_nonneg {P : Matrix n n ℝ} (hP : P.PosSemidef) (x : n → ℝ) :
    0 ≤ energy P x := by simpa [energy] using hP.dotProduct_mulVec_nonneg x

variable [DecidableEq n]

lemma energy_identity (x : n → ℝ) : energy (1 : Matrix n n ℝ) x = ∑ i, x i ^ 2 := by
  simp [energy, dotProduct, pow_two]

lemma energy_step {A P : Matrix n n ℝ} (h : stein A P = 1) (x : n → ℝ) :
    energy P x - energy P (A *ᵥ x) = ∑ i, x i ^ 2 := by
  have hx := congrArg (fun M => energy M x) h
  have he : energy (stein A P) x = energy P x - energy P (A *ᵥ x) := by
    rw [← energy_conjugate]
    simp [stein, energy, sub_mulVec, dotProduct_sub]
  rw [he, energy_identity] at hx
  exact hx

lemma energy_telescope {A P : Matrix n n ℝ} (h : stein A P = 1)
    (x : n → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, ∑ i, ((A ^ k *ᵥ x) i) ^ 2 =
      energy P x - energy P (A ^ N *ᵥ x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have he := energy_step h (A ^ N *ᵥ x)
    rw [pow_succ', ← mulVec_mulVec]
    linarith

theorem tendsto_pow_zero_of_lyapunov {A P : Matrix n n ℝ}
    (hP : P.PosDef) (h : stein A P = 1) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  have hs (x : n → ℝ) : Summable (fun k : ℕ => ∑ i, ((A ^ k *ᵥ x) i) ^ 2) := by
    apply summable_of_sum_range_le (c := energy P x)
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    intro N
    rw [energy_telescope h]
    exact sub_le_self _ (energy_nonneg hP.posSemidef _)
  have hc (i j : n) : Summable (fun k : ℕ => ((A ^ k) i j) ^ 2) := by
    have hx := hs (Pi.single j 1)
    simp only [mulVec_single, MulOpposite.op_one, one_smul, col_apply] at hx
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k =>
      Finset.single_le_sum (fun l _ => sq_nonneg ((A ^ k) l j)) (Finset.mem_univ i)) hx
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have ht := (Real.continuous_sqrt.tendsto 0).comp (hc i j).tendsto_atTop_zero
  have hab : Tendsto (fun k : ℕ => ‖(A ^ k) i j‖) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hab

theorem summable_pow_of_lyapunov {A P : Matrix n n ℝ}
    (hP : P.PosDef) (h : stein A P = 1) : Summable (fun k : ℕ => A ^ k) :=
  (summable_pow_iff_tendsto_zero A).mpr (tendsto_pow_zero_of_lyapunov hP h)

theorem stein_kernel_eq_zero {A X : Matrix n n ℝ}
    (hA : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)) (hX : stein A X = 0) : X = 0 := by
  have he : ∀ k : ℕ, (A ^ k)ᵀ * X * A ^ k = X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hx : Aᵀ * X * A = X := (sub_eq_zero.mp hX).symm
      calc
        (A ^ (k + 1))ᵀ * X * A ^ (k + 1) =
            (A ^ k)ᵀ * (Aᵀ * X * A) * A ^ k := by
          rw [pow_succ', transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = X := by rw [hx, ih]
  have hT : Tendsto (fun k : ℕ => (A ^ k)ᵀ) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (continuous_id.matrix_transpose.tendsto (0 : Matrix n n ℝ)).comp hA
  have ht := (hT.mul_const X).mul hA
  simp only [zero_mul, mul_zero] at ht
  exact tendsto_nhds_unique tendsto_const_nhds (ht.congr he)

def gram (A : Matrix n n ℝ) (k : ℕ) : Matrix n n ℝ := (A ^ k)ᵀ * A ^ k

lemma gram_posSemidef (A : Matrix n n ℝ) (k : ℕ) : (gram A k).PosSemidef := by
  simpa [gram] using posSemidef_conjTranspose_mul_self (A ^ k)

lemma gram_succ (A : Matrix n n ℝ) (k : ℕ) :
    gram A (k + 1) = Aᵀ * gram A k * A := by
  simp only [gram, pow_succ, transpose_mul, Matrix.mul_assoc]

open scoped Matrix.Norms.Operator in
theorem summable_gram {A : Matrix n n ℝ} (hA : Summable (fun k : ℕ => A ^ k)) :
    Summable (gram A) := by
  have hT : Tendsto (fun k : ℕ => (A ^ k)ᵀ) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_id.matrix_transpose.tendsto (0 : Matrix n n ℝ)).comp
      hA.tendsto_atTop_zero
  apply Summable.of_norm_bounded_eventually_nat hA.norm
  filter_upwards [hT.norm.eventually (gt_mem_nhds (by simp : ‖(0 : Matrix n n ℝ)‖ < 1))]
    with k hk
  exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (A ^ k)])

noncomputable def lyapunovSolution (A : Matrix n n ℝ) : Matrix n n ℝ := ∑' k, gram A k

def energyLinear (x : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun P := energy P x
  map_add' P Q := by simp [energy, add_mulVec, dotProduct_add]
  map_smul' c P := by simp [energy, smul_mulVec, dotProduct_smul]

open scoped Matrix.Norms.Operator in
theorem lyapunovSolution_posDef {A : Matrix n n ℝ}
    (hA : Summable (fun k : ℕ => A ^ k)) : (lyapunovSolution A).PosDef := by
  have hg := summable_gram hA
  apply PosDef.of_dotProduct_mulVec_pos
  · change (lyapunovSolution A)ᵀ = lyapunovSolution A
    simp [lyapunovSolution, transpose_tsum, gram, transpose_mul]
  · intro x hx
    have hs := hg.hasSum.map (energyLinear x).toAddMonoidHom
      (energyLinear x).continuous_of_finiteDimensional
    have hn (k : ℕ) : 0 ≤ energy (gram A k) x := energy_nonneg (gram_posSemidef A k) x
    have hp : 0 < energy (gram A 0) x := by
      simpa [gram, energy] using (PosDef.one : (1 : Matrix n n ℝ).PosDef).dotProduct_mulVec_pos hx
    have hl := hs.summable.le_tsum 0 (fun k _ => hn k)
    rw [hs.tsum_eq] at hl
    simpa [energyLinear, energy, lyapunovSolution] using hp.trans_le hl

theorem stein_lyapunovSolution {A : Matrix n n ℝ}
    (hA : Summable (fun k : ℕ => A ^ k)) : stein A (lyapunovSolution A) = 1 := by
  have hg := summable_gram hA
  have he : Aᵀ * lyapunovSolution A * A = ∑' k, gram A (k + 1) := by
    rw [lyapunovSolution, ← hg.tsum_mul_left, ← (hg.mul_left Aᵀ).tsum_mul_right]
    exact tsum_congr (fun k => (gram_succ A k).symm)
  rw [stein, he, lyapunovSolution, hg.tsum_eq_zero_add]
  simp [gram]

theorem summable_pow_iff_lyapunov (A : Matrix n n ℝ) :
    Summable (fun k : ℕ => A ^ k) ↔ ∃ P, P.PosDef ∧ stein A P = 1 := by
  exact ⟨fun h => ⟨lyapunovSolution A, lyapunovSolution_posDef h, stein_lyapunovSolution h⟩,
    fun ⟨_, hp, he⟩ => summable_pow_of_lyapunov hp he⟩

end SympyProofs.NeumannSeries
