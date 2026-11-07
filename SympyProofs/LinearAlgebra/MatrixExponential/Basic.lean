module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Analysis.Matrix.Normed

/-!
# Matrix exponential

The exponential of a finite square matrix over `ℝ` or `ℂ`, defined using mathlib's
convergent power series. Matrix powers in this series use matrix multiplication;
this is not the entrywise exponential. No norm on matrices is exported.

The adjoint and entrywise conjugation identities for `exp (z • A)` explain why
the scalar must be conjugated. Applying them to complex powers `A ^ z` additionally
requires a compatible choice of matrix logarithm; see `MatrixPower.Basic`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]

/-- The matrix exponential `∑ k, (k!)⁻¹ • A^k`. -/
noncomputable def exp (A : Matrix n n 𝕂) : Matrix n n 𝕂 :=
  NormedSpace.exp A

theorem exp_eq_tsum (A : Matrix n n 𝕂) :
    exp A = ∑' k : ℕ, ((Nat.factorial k : 𝕂)⁻¹) • A ^ k := by
  exact congrFun (NormedSpace.exp_eq_tsum 𝕂) A

/-- The defining series converges for every finite real or complex matrix. -/
theorem hasSum_exp (A : Matrix n n 𝕂) :
    HasSum (fun k : ℕ => ((Nat.factorial k : 𝕂)⁻¹) • A ^ k) (exp A) := by
  open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' A

@[simp] theorem exp_zero : exp (0 : Matrix n n 𝕂) = 1 :=
  NormedSpace.exp_zero

theorem exp_add_of_commute (A B : Matrix n n 𝕂) (h : Commute A B) :
    exp (A + B) = exp A * exp B :=
  Matrix.exp_add_of_commute A B h

theorem isUnit_exp (A : Matrix n n 𝕂) : IsUnit (exp A) :=
  Matrix.isUnit_exp A

theorem exp_neg (A : Matrix n n 𝕂) : exp (-A) = (exp A)⁻¹ :=
  Matrix.exp_neg A

theorem exp_natCast_smul (A : Matrix n n 𝕂) (k : ℕ) :
    exp ((k : 𝕂) • A) = exp A ^ k := by
  simpa only [exp, Nat.cast_smul_eq_nsmul] using Matrix.exp_nsmul k A

@[simp] theorem exp_transpose (A : Matrix n n 𝕂) : exp Aᵀ = (exp A)ᵀ :=
  Matrix.exp_transpose A

@[simp] theorem exp_conjTranspose (A : Matrix n n 𝕂) : exp Aᴴ = (exp A)ᴴ :=
  Matrix.exp_conjTranspose A

/-- Entrywise conjugation, as distinct from the adjoint `Aᴴ`. -/
@[simp] theorem exp_map_star (A : Matrix n n 𝕂) :
    exp (A.map star) = (exp A).map star := by
  calc
    exp (A.map star) = exp Aᴴᵀ := rfl
    _ = (exp Aᴴ)ᵀ := exp_transpose _
    _ = (exp A)ᴴᵀ := congrArg Matrix.transpose (exp_conjTranspose A)
    _ = (exp A).map star := rfl

theorem conjTranspose_exp_smul (A : Matrix n n 𝕂) (z : 𝕂) :
    (exp (z • A))ᴴ = exp (star z • Aᴴ) := by
  rw [← exp_conjTranspose, Matrix.conjTranspose_smul]

theorem map_star_exp_smul (A : Matrix n n 𝕂) (z : 𝕂) :
    (exp (z • A)).map star = exp (star z • A.map star) := by
  rw [← exp_map_star]
  congr 1
  ext i j
  simp [Matrix.map_apply, smul_eq_mul]

theorem exp_diagonal_complex (d : n → ℂ) :
    exp (Matrix.diagonal d) = Matrix.diagonal (fun i => Complex.exp (d i)) := by
  rw [exp, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Complex.exp_eq_exp_ℂ]
  exact (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) d) i).unique
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (d i))

theorem exp_diagonal_real (d : n → ℝ) :
    exp (Matrix.diagonal d) = Matrix.diagonal (fun i => Real.exp (d i)) := by
  rw [exp, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Real.exp_eq_exp_ℝ]
  exact (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) d) i).unique
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (d i))

end SympyProofs.MatrixExponential
