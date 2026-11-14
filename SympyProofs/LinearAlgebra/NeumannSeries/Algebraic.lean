module

public import SympyProofs.LinearAlgebra.NeumannSeries.Lyapunov
public import SympyProofs.LinearAlgebra.NeumannSeries.Sylvester

/-!
# A finite polynomial test for convergence

We use all `n²` matrix coordinates. This avoids choosing a basis of the symmetric
subspace; uniqueness automatically makes the reconstructed solution symmetric.
-/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

variable {n : Type*}

def vec {R : Type*} (P : Matrix n n R) : n × n → R := fun ij => P ij.1 ij.2

def unvec {R : Type*} (p : n × n → R) : Matrix n n R := fun i j => p (i, j)

@[simp] lemma vec_unvec {R : Type*} (p : n × n → R) : vec (unvec p) = p := rfl
@[simp] lemma unvec_vec {R : Type*} (P : Matrix n n R) : unvec (vec P) = P := rfl

lemma vec_injective {R : Type*} : Function.Injective (vec (n := n) (R := R)) :=
  fun _ _ h => congrArg unvec h

variable [Fintype n] [DecidableEq n]

/-- Coefficient matrix of `P ↦ P - Aᵀ P A`, in all matrix coordinates. -/
def steinMatrix {R : Type*} [CommRing R] (A : Matrix n n R) : Matrix (n × n) (n × n) R :=
  1 - of (fun ij kl => A kl.1 ij.1 * A kl.2 ij.2)

lemma steinMatrix_mulVec (A P : Matrix n n ℝ) :
    steinMatrix A *ᵥ vec P = vec (stein A P) := by
  rw [steinMatrix, sub_mulVec, one_mulVec]
  ext ⟨i, j⟩
  simp only [Pi.sub_apply, mulVec, dotProduct,
    of_apply, vec, stein, Matrix.sub_apply, mul_apply, transpose_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- All coefficients are obtained by ring operations and determinants. -/
def denominator {R : Type*} [CommRing R] (A : Matrix n n R) : R := (steinMatrix A).det

def numerator {R : Type*} [CommRing R] (A : Matrix n n R) : Matrix n n R :=
  unvec ((steinMatrix A).adjugate *ᵥ vec (1 : Matrix n n R))

noncomputable def candidate (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (denominator A)⁻¹ • numerator A

theorem denominator_ne_zero {A : Matrix n n ℝ}
    (hA : Summable (fun k : ℕ => A ^ k)) : denominator A ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : steinMatrix A *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have hx : stein A (unvec (x - y)) = 0 := by
    apply vec_injective
    rw [← steinMatrix_mulVec, vec_unvec, hz]
    rfl
  have he := stein_kernel_eq_zero hA.tendsto_atTop_zero hx
  have he' := congrArg vec he
  exact sub_eq_zero.mp he'

lemma stein_injective_of_denominator_ne_zero {A : Matrix n n ℝ}
    (hd : denominator A ≠ 0) : Function.Injective (stein A) := by
  intro P Q hpq
  apply vec_injective
  apply Matrix.mulVec_injective_of_det_ne_zero hd
  rw [steinMatrix_mulVec, steinMatrix_mulVec, hpq]

theorem stein_candidate {A : Matrix n n ℝ} (hd : denominator A ≠ 0) :
    stein A (candidate A) = 1 := by
  apply vec_injective
  rw [← steinMatrix_mulVec]
  change steinMatrix A *ᵥ ((denominator A)⁻¹ •
    ((steinMatrix A).adjugate *ᵥ vec (1 : Matrix n n ℝ))) = vec 1
  rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec,
    smul_smul, show (denominator A)⁻¹ * (steinMatrix A).det = 1 from inv_mul_cancel₀ hd,
    one_smul]

theorem candidate_isHermitian {A : Matrix n n ℝ} (hd : denominator A ≠ 0) :
    (candidate A).IsHermitian := by
  change (candidate A)ᵀ = candidate A
  apply stein_injective_of_denominator_ne_zero hd
  have ht := congrArg Matrix.transpose (stein_candidate hd)
  rw [stein_candidate hd]
  simpa [stein, transpose_sub, transpose_mul, Matrix.mul_assoc] using ht

theorem summable_pow_iff_candidate (A : Matrix n n ℝ) :
    Summable (fun k : ℕ => A ^ k) ↔ denominator A ≠ 0 ∧ (candidate A).PosDef := by
  constructor
  · intro h
    have hd := denominator_ne_zero h
    have he : candidate A = lyapunovSolution A :=
      stein_injective_of_denominator_ne_zero hd ((stein_candidate hd).trans
        (stein_lyapunovSolution h).symm)
    exact ⟨hd, he ▸ lyapunovSolution_posDef h⟩
  · rintro ⟨hd, hp⟩
    exact summable_pow_of_lyapunov hp (stein_candidate hd)

/-- The finite family of polynomial inequalities; there are no auxiliary real variables. -/
def algebraicCondition {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  denominator A ≠ 0 ∧ ∀ k : Fin (m + 1),
    0 < denominator A ^ k.val * (leading (numerator A) k).det

lemma leading_candidate_det {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (k : Fin (m + 1)) :
    (leading (candidate A) k).det = (denominator A ^ k.val)⁻¹ *
      (leading (numerator A) k).det := by
  change ((denominator A)⁻¹ • leading (numerator A) k).det = _
  rw [det_smul, Fintype.card_fin, inv_pow]

lemma clear_denominator_pos {d r : ℝ} :
    0 < d⁻¹ * r ↔ 0 < d * r := by
  simp only [mul_pos_iff, inv_pos, inv_lt_zero]

/-- Matrix Neumann series convergence is exactly a finite conjunction of polynomial signs. -/
theorem summable_pow_iff_algebraicCondition {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Summable (fun k : ℕ => A ^ k) ↔ algebraicCondition A := by
  rw [summable_pow_iff_candidate, algebraicCondition]
  apply and_congr_right
  intro hd
  rw [posDef_iff_leading_pos, and_iff_right (candidate_isHermitian hd)]
  apply forall_congr'
  intro k
  rw [leading_candidate_det, clear_denominator_pos]

theorem hasSum_inverse_of_algebraicCondition {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (h : algebraicCondition A) : HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ :=
  hasSum_inverse ((summable_pow_iff_algebraicCondition A).mpr h)

end SympyProofs.NeumannSeries
