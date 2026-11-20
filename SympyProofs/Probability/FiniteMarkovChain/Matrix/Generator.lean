module

public import SympyProofs.LinearAlgebra.MatrixExponential.Basic
public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith

/-!
# Generators and their transition matrices

This file is about matrices only. No probability space appears in it.

A continuous-time generator is a real square matrix with nonnegative off-diagonal
entries and zero row sums. This is `IsGenerator`.

The transition matrix of `Q` over time `t` is the matrix exponential `exp (t • Q)`.
This is `transition Q t`. It satisfies the semigroup law and the forward equation,
and its derivative at time `0` recovers `Q`. For a generator and nonnegative time it
is row stochastic. Conversely, only generators have row-stochastic exponentials at
all nonnegative times.

Nonnegativity follows by shifting the generator by a scalar identity matrix and
using the exponential series of the resulting entrywise nonnegative matrix. The same
series shows that the diagonal entries are positive: the chain stays where it is with
positive probability. It also shows that an entry is positive at every positive time
when the matching entry of the generator is positive.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι]

/-! ### Generators -/

/-- A finite-state continuous-time Markov generator in the row convention. -/
structure IsGenerator (Q : Matrix ι ι ℝ) : Prop where
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  row_sum_zero : ∀ i, ∑ j, Q i j = 0

theorem IsGenerator.mulVec_one_eq_zero {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) :
    Q *ᵥ (1 : ι → ℝ) = 0 := by
  ext i
  simpa [mulVec, dotProduct] using hQ.row_sum_zero i

/-- Every row vector has zero total mass after multiplication by a generator. -/
theorem IsGenerator.sum_vecMul_eq_zero {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (w : ι → ℝ) : ∑ i, (w ᵥ* Q) i = 0 := by
  rw [← dotProduct_one, ← dotProduct_mulVec, hQ.mulVec_one_eq_zero, dotProduct_zero]

@[simp] theorem isGenerator_zero : IsGenerator (0 : Matrix ι ι ℝ) := by
  constructor <;> simp

variable [DecidableEq ι]

/-! ### Definition and semigroup law -/

/-- The matrix exponential giving continuous-time evolution. -/
noncomputable def transition (Q : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  MatrixExponential.exp (t • Q)

@[simp] theorem transition_zero (Q : Matrix ι ι ℝ) : transition Q 0 = 1 := by
  simp [transition]

@[simp] theorem transition_zero_generator (t : ℝ) :
    transition (0 : Matrix ι ι ℝ) t = 1 := by
  simp [transition]

/-- The exponential satisfies the time-homogeneous semigroup law. -/
theorem transition_add (Q : Matrix ι ι ℝ) (s t : ℝ) :
    transition Q (s + t) = transition Q s * transition Q t := by
  unfold transition
  rw [add_smul]
  exact MatrixExponential.exp_add_of_commute _ _
    (((Commute.refl Q).smul_left s).smul_right t)

theorem vecMul_transition_add (Q : Matrix ι ι ℝ) (w : ι → ℝ) (s t : ℝ) :
    w ᵥ* transition Q (s + t) = (w ᵥ* transition Q s) ᵥ* transition Q t := by
  simp only [transition_add, vecMul_vecMul]

/-- Differentiating the exponential gives the forward evolution equation,
written with the generator acting first. -/
theorem hasDerivAt_vecMul_transition (Q : Matrix ι ι ℝ) (w : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => w ᵥ* transition Q s) ((w ᵥ* Q) ᵥ* transition Q t) t := by
  open scoped Matrix.Norms.Operator in
    let L : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
      { toLinearMap := Matrix.vecMulBilin ℝ ℝ w
        cont := continuous_const.matrix_vecMul continuous_id }
    have h := L.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_exp_smul_const' Q t)
    change HasDerivAt (fun s => w ᵥ* MatrixExponential.exp (s • Q))
      (w ᵥ* (Q * MatrixExponential.exp (t • Q))) t at h
    change HasDerivAt (fun s => w ᵥ* MatrixExponential.exp (s • Q))
      ((w ᵥ* Q) ᵥ* MatrixExponential.exp (t • Q)) t
    simpa only [vecMul_vecMul] using h

/-- Each entry of the transition matrix has the generator entry as its derivative at
time zero. -/
theorem hasDerivAt_transition_apply_zero (Q : Matrix ι ι ℝ) (i j : ι) :
    HasDerivAt (fun t => transition Q t i j) (Q i j) 0 := by
  have h := hasDerivAt_pi.mp (hasDerivAt_vecMul_transition Q (Pi.single i 1) 0) j
  simpa using h

/-- A row of a matrix is determined by the same row of its transition matrices at
nonnegative times. -/
theorem transition_row_injective {Q Q' : Matrix ι ι ℝ} {i : ι}
    (h : ∀ (t : ℝ≥0) (j : ι), transition Q t i j = transition Q' t i j) (j : ι) :
    Q i j = Q' i j := by
  have hd := (hasDerivAt_transition_apply_zero Q i j).hasDerivWithinAt (s := Set.Ici 0)
  have hd' : HasDerivWithinAt (fun t => transition Q t i j) (Q' i j) (Set.Ici 0) 0 :=
    (hasDerivAt_transition_apply_zero Q' i j).hasDerivWithinAt.congr
      (fun t ht => h ⟨t, ht⟩ j) (by simp)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd hd'

/-- A matrix is determined by its transition matrices at nonnegative times. -/
theorem transition_injective {Q Q' : Matrix ι ι ℝ}
    (h : ∀ t : ℝ≥0, transition Q t = transition Q' t) : Q = Q' := by
  ext i j
  exact transition_row_injective (fun t j => congrFun (congrFun (h t) i) j) j

/-! ### Rows fixed by the transition matrix -/

/-- A row annihilated by `Q` is unchanged at every real time, negative times included. -/
theorem vecMul_transition_of_vecMul_eq_zero {Q : Matrix ι ι ℝ} {w : ι → ℝ} (h : w ᵥ* Q = 0)
    (t : ℝ) : w ᵥ* transition Q t = w := by
  have hd (s : ℝ) : HasDerivAt (fun s => w ᵥ* transition Q s) 0 s := by
    simpa only [h, zero_vecMul] using hasDerivAt_vecMul_transition Q w s
  simpa using is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

/-! ### Stochasticity -/

private theorem pow_apply_nonneg (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k hk =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hk i l) (hA l j)

private theorem exp_nonneg_of_nonneg (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (i j : ι) : 0 ≤ MatrixExponential.exp A i j := by
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp A) i) j
  rw [← hs.tsum_eq]
  exact tsum_nonneg fun k =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_apply_nonneg A hA k i j)

private theorem one_le_exp_diag (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (i : ι) :
    1 ≤ MatrixExponential.exp A i i := by
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp A) i) i
  have h0 := le_hasSum hs 0 fun k _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_apply_nonneg A hA k i i)
  simpa using h0

private theorem le_exp_apply (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (i j : ι) :
    A i j ≤ MatrixExponential.exp A i j := by
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp A) i) j
  have h1 := le_hasSum hs 1 fun k _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_apply_nonneg A hA k i j)
  simpa using h1

private theorem exp_smul_one (c : ℝ) :
    MatrixExponential.exp (c • (1 : Matrix ι ι ℝ)) = Real.exp c • 1 := by
  have hd (r : ℝ) : r • (1 : Matrix ι ι ℝ) = diagonal (fun _ => r) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hd, MatrixExponential.exp_diagonal_real, ← hd]

/-- Adding a large multiple of the identity makes every entry nonnegative, and the
transition matrix is a positive multiple of the exponential of the shifted matrix. -/
private theorem exists_transition_eq_smul_exp (Q : Matrix ι ι ℝ)
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (t : ℝ) :
    ∃ c : ℝ, (∀ i j, 0 ≤ (Q + c • 1) i j) ∧
      transition Q t = Real.exp (-(t * c)) • MatrixExponential.exp (t • (Q + c • 1)) := by
  let c : ℝ := ∑ k, |Q k k|
  have hshift : ∀ i j, 0 ≤ (Q + c • 1) i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hc : |Q i i| ≤ c :=
        Finset.single_le_sum (fun k _ => abs_nonneg (Q k k)) (Finset.mem_univ i)
      have hi := neg_abs_le (Q i i)
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one]
      linarith
    · simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using hQ i j hij
  have hsplit : t • Q = t • (Q + c • 1) + (-(t * c)) • 1 := by
    simp [smul_add, smul_smul, neg_smul]
  have hcomm : Commute (t • (Q + c • 1)) ((-(t * c)) • (1 : Matrix ι ι ℝ)) :=
    (Commute.one_right _).smul_right _
  refine ⟨c, hshift, ?_⟩
  unfold transition
  rw [hsplit, MatrixExponential.exp_add_of_commute _ _ hcomm, exp_smul_one,
    mul_smul_comm, mul_one]

/-- Exponentials of real matrices with nonnegative off-diagonal entries are
entrywise nonnegative at nonnegative times. Zero row sums are not required. -/
theorem transition_nonneg_of_offDiag_nonneg (Q : Matrix ι ι ℝ)
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (t : ℝ) (ht : 0 ≤ t) (i j : ι) :
    0 ≤ transition Q t i j := by
  obtain ⟨c, hshift, he⟩ := exists_transition_eq_smul_exp Q hQ t
  rw [he]
  exact mul_nonneg (Real.exp_pos _).le
    (exp_nonneg_of_nonneg _ (fun k l => mul_nonneg ht (hshift k l)) i j)

/-- Over any nonnegative time the chain stays in its state with positive probability.
Zero row sums are not required. -/
theorem transition_diag_pos_of_offDiag_nonneg (Q : Matrix ι ι ℝ)
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (t : ℝ) (ht : 0 ≤ t) (i : ι) :
    0 < transition Q t i i := by
  obtain ⟨c, hshift, he⟩ := exists_transition_eq_smul_exp Q hQ t
  rw [he]
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le one_pos
    (one_le_exp_diag _ (fun k l => mul_nonneg ht (hshift k l)) i))

/-- Over any positive time the chain moves along a positive rate with positive
probability. Zero row sums are not required. -/
theorem transition_pos_of_pos (Q : Matrix ι ι ℝ)
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) (t : ℝ) (ht : 0 < t) {i j : ι} (h : 0 < Q i j) :
    0 < transition Q t i j := by
  rcases eq_or_ne i j with rfl | hij
  · exact transition_diag_pos_of_offDiag_nonneg Q hQ t ht.le i
  obtain ⟨c, hshift, he⟩ := exists_transition_eq_smul_exp Q hQ t
  rw [he]
  have hle := le_exp_apply _ (fun k l => mul_nonneg ht.le (hshift k l)) i j
  have hpos : 0 < (t • (Q + c • 1)) i j := by
    simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using mul_pos ht h
  exact mul_pos (Real.exp_pos _) (hpos.trans_le hle)

/-- Zero row sums imply that the exponential has row sums one at every real time. -/
theorem transition_mulVec_one (Q : Matrix ι ι ℝ)
    (hQ : Q *ᵥ (1 : ι → ℝ) = 0) (t : ℝ) :
    transition Q t *ᵥ (1 : ι → ℝ) = 1 := by
  have hb : (1 : ι → ℝ) ᵥ* Qᵀ = 0 := by
    simpa [vecMul_transpose] using hQ
  have ht : transition Qᵀ t = (transition Q t)ᵀ := by
    simp only [transition, ← transpose_smul, MatrixExponential.exp_transpose]
  simpa only [ht, vecMul_transpose] using vecMul_transition_of_vecMul_eq_zero hb t

/-- A transition matrix preserves the total mass of a row. -/
theorem sum_vecMul_transition {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) (x : ι → ℝ)
    (t : ℝ) :
    ∑ j, (x ᵥ* transition Q t) j = ∑ j, x j := by
  rw [← dotProduct_one, ← dotProduct_mulVec, transition_mulVec_one Q hQ.mulVec_one_eq_zero t,
    dotProduct_one]

/-- The exponential of a finite-state generator is row stochastic for `t ≥ 0`. -/
theorem IsGenerator.transition_mem_rowStochastic {Q : Matrix ι ι ℝ}
    (hQ : IsGenerator Q) (t : ℝ) (ht : 0 ≤ t) :
    transition Q t ∈ Matrix.rowStochastic ℝ ι :=
  ⟨transition_nonneg_of_offDiag_nonneg Q hQ.offDiag_nonneg t ht,
    transition_mulVec_one Q hQ.mulVec_one_eq_zero t⟩

/-- A matrix whose exponentials are row stochastic at nonnegative times is a generator. -/
theorem isGenerator_of_transition_mem_rowStochastic {Q : Matrix ι ι ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → transition Q t ∈ Matrix.rowStochastic ℝ ι) : IsGenerator Q := by
  constructor
  · intro i j hij
    have hd := (hasDerivAt_transition_apply_zero Q i j).hasDerivWithinAt (s := Set.Ioi 0)
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
    refine ge_of_tendsto hd (eventually_mem_nhdsWithin.mono fun t ht => ?_)
    have h0 : transition Q 0 i j = 0 := by simp [hij]
    rw [slope_def_field, h0, sub_zero, sub_zero]
    exact div_nonneg ((h t (le_of_lt ht)).1 i j) (le_of_lt ht)
  · intro i
    have hd : HasDerivWithinAt (fun t => ∑ j, transition Q t i j) (∑ j, Q i j) (Set.Ici 0) 0 :=
      (HasDerivAt.fun_sum fun j _ => hasDerivAt_transition_apply_zero Q i j).hasDerivWithinAt
    have hc : HasDerivWithinAt (fun t => ∑ j, transition Q t i j) 0 (Set.Ici 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (1 : ℝ)).congr
        (fun t ht => Matrix.sum_row_of_mem_rowStochastic (h t ht) i) (by simp [Matrix.one_apply])
    exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd hc

/-- Generators are exactly the matrices with row-stochastic exponentials. -/
theorem isGenerator_iff_transition_mem_rowStochastic (Q : Matrix ι ι ℝ) :
    IsGenerator Q ↔ ∀ t : ℝ, 0 ≤ t → transition Q t ∈ Matrix.rowStochastic ℝ ι :=
  ⟨fun hQ t ht => hQ.transition_mem_rowStochastic t ht,
    isGenerator_of_transition_mem_rowStochastic⟩

end SympyProofs.FiniteMarkovChain
