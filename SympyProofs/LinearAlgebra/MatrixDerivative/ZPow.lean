module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Pow
public import SympyProofs.LinearAlgebra.MatrixDerivative.Inverse
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Matrix.ZPow

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of integer powers of nonsingular matrices.
Negative powers are natural powers of the inverse, so their derivatives follow
from the inverse and natural-power rules. Invertibility is required only at the
point of differentiation, and no commutativity with the derivative is assumed.
The general rule uses a signed sum over the integer interval between zero and
the exponent, with no case distinction in the theorem statement. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- The negative-power rule, including the zero exponent as an empty sum. -/
theorem hasDerivAt_zpow_neg [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) (k : ℕ) :
    HasDerivAt (fun s => M s ^ (-(k : ℤ)))
      (-(∑ i ∈ Finset.range k, (M t)⁻¹ ^ (k - i) * M' * (M t)⁻¹ ^ (i + 1))) t := by
  have h := hasDerivAt_pow (hasDerivAt_inv hM hunit) k
  simp only [Matrix.zpow_neg_natCast, ← Matrix.inv_pow']
  convert h using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hexp : k - 1 - i + 1 = k - i := by
    have := Finset.mem_range.mp hi
    omega
  simp only [neg_mul, mul_neg, mul_assoc]
  rw [← mul_assoc ((M t)⁻¹ ^ (k - 1 - i)), ← pow_succ, hexp,
    ← pow_succ']

theorem deriv_zpow_neg [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) (k : ℕ) :
    deriv (fun s => M s ^ (-(k : ℤ))) t =
      -(∑ i ∈ Finset.range k, (M t)⁻¹ ^ (k - i) * M' * (M t)⁻¹ ^ (i + 1)) := by
  open scoped Matrix.Norms.Operator in
    simpa using! (hasDerivAt_zpow_neg hM hunit k).deriv

private theorem sum_Ico_zpow_nat [Fintype n] [DecidableEq n]
    (A D : Matrix n n 𝕜) (k : ℕ) :
    (∑ i ∈ Finset.Ico 0 (k : ℤ), A ^ i * D * A ^ ((k : ℤ) - 1 - i)) =
      ∑ i ∈ Finset.range k, A ^ (k - 1 - i) * D * A ^ i := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp only [sub_zero, Int.toNat_natCast, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, zero_add]
  rw [← Finset.sum_range_reflect
    (fun i : ℕ => A ^ (i : ℤ) * D * A ^ ((k : ℤ) - 1 - i)) k]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (k : ℤ) - 1 - (k - 1 - i : ℕ) = i := by
    have := Finset.mem_range.mp hi
    omega
  simp only [he, zpow_natCast]

private theorem sum_Ico_zpow_neg [Fintype n] [DecidableEq n]
    (A D : Matrix n n 𝕜) (k : ℕ) :
    (∑ i ∈ Finset.Ico (-(k : ℤ)) 0, A ^ i * D * A ^ (-(k : ℤ) - 1 - i)) =
      ∑ i ∈ Finset.range k, A⁻¹ ^ (k - i) * D * A⁻¹ ^ (i + 1) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp only [zero_sub, neg_neg, Int.toNat_natCast, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have he₁ : -(k : ℤ) + i = -((k - i : ℕ) : ℤ) := by
    have := Finset.mem_range.mp hi
    omega
  have he₂ : -(k : ℤ) - 1 - (-(k : ℤ) + i) = -((i + 1 : ℕ) : ℤ) := by omega
  rw [he₂, he₁]
  simp only [Matrix.zpow_neg_natCast, ← Matrix.inv_pow']

/-- The ordered power rule for every integer exponent as a signed interval sum.
For zero the sum is empty; for negative exponents the sign reverses the sum. -/
theorem hasDerivAt_zpow [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) (z : ℤ) :
    HasDerivAt (fun s => M s ^ z)
      (z.sign • ∑ i ∈ Finset.Ico (min 0 z) (max 0 z),
        M t ^ i * M' * M t ^ (z - 1 - i)) t := by
  cases z with
  | ofNat k =>
    cases k with
    | zero => simpa using hasDerivAt_pow hM 0
    | succ k =>
      simp only [Int.ofNat_eq_natCast]
      rw [min_eq_left (Int.natCast_nonneg (k + 1)), max_eq_right (Int.natCast_nonneg (k + 1)),
        Int.sign_natCast_of_ne_zero (Nat.succ_ne_zero _), one_smul, sum_Ico_zpow_nat]
      simpa only [zpow_natCast] using hasDerivAt_pow hM (k + 1)
  | negSucc k =>
    rw [min_eq_right (Int.negSucc_le_zero _), max_eq_left (Int.negSucc_le_zero _),
      Int.sign_negSucc, neg_one_zsmul]
    change HasDerivAt (fun s => M s ^ (-((k + 1 : ℕ) : ℤ)))
      (-(∑ i ∈ Finset.Ico (-((k + 1 : ℕ) : ℤ)) 0,
        M t ^ i * M' * M t ^ (-((k + 1 : ℕ) : ℤ) - 1 - i))) t
    rw [sum_Ico_zpow_neg]
    exact hasDerivAt_zpow_neg hM hunit (k + 1)

theorem deriv_zpow [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) (z : ℤ) :
    deriv (fun s => M s ^ z) t =
      z.sign • ∑ i ∈ Finset.Ico (min 0 z) (max 0 z),
        M t ^ i * M' * M t ^ (z - 1 - i) := by
  open scoped Matrix.Norms.Operator in
    simpa using! (hasDerivAt_zpow hM hunit z).deriv

/-- A nonzero determinant supplies the nonsingularity hypothesis. -/
theorem hasDerivAt_zpow_of_det_ne_zero [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hdet : (M t).det ≠ 0) (z : ℤ) :
    HasDerivAt (fun s => M s ^ z)
      (z.sign • ∑ i ∈ Finset.Ico (min 0 z) (max 0 z),
        M t ^ i * M' * M t ^ (z - 1 - i)) t :=
  hasDerivAt_zpow hM
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)) z

end SympyProofs.MatrixDerivative
