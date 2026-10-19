import SympyProofs.MoorePenrose.Basic

/-!
# Moore–Penrose pseudoinverses of row and column matrices

For a nonzero real or complex vector, the pseudoinverse of its row or column
matrix is its conjugate transpose divided by the conjugate dot product
`star v ⬝ᵥ v`. For the zero vector it is zero. We verify all four Penrose
equations and prove uniqueness, for arbitrary finite index types (including
the empty type).

Lean's convention `0⁻¹ = 0` lets the definitions use the same expression in
both cases; the zero case is also stated explicitly.
-/

namespace SympyProofs.MoorePenrose

open Matrix
open scoped ComplexOrder

section Vectors

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The candidate pseudoinverse of a `1 × n` matrix. -/
noncomputable def rowPinv (A : Matrix (Fin 1) n 𝕜) : Matrix n (Fin 1) 𝕜 :=
  (star (A 0) ⬝ᵥ A 0)⁻¹ • Aᴴ

/-- The candidate pseudoinverse of an `n × 1` matrix. -/
noncomputable def colPinv (A : Matrix n (Fin 1) 𝕜) : Matrix (Fin 1) n 𝕜 :=
  (star (fun i => A i 0) ⬝ᵥ (fun i => A i 0))⁻¹ • Aᴴ

@[simp] theorem rowPinv_zero : rowPinv (0 : Matrix (Fin 1) n 𝕜) = 0 := by
  simp [rowPinv]

@[simp] theorem colPinv_zero : colPinv (0 : Matrix n (Fin 1) 𝕜) = 0 := by
  simp [colPinv]

/-- Entrywise row formula: divide the conjugate entry by the conjugate dot product. -/
theorem rowPinv_apply (A : Matrix (Fin 1) n 𝕜) (i : n) (j : Fin 1) :
    rowPinv A i j = star (A j i) / (star (A 0) ⬝ᵥ A 0) := by
  simp [rowPinv, div_eq_mul_inv, mul_comm]

/-- Entrywise column formula: divide the conjugate entry by the conjugate dot product. -/
theorem colPinv_apply (A : Matrix n (Fin 1) 𝕜) (i : Fin 1) (j : n) :
    colPinv A i j = star (A j i) / (star (fun k => A k 0) ⬝ᵥ (fun k => A k 0)) := by
  simp [colPinv, div_eq_mul_inv, mul_comm]

/-- Over the reals the row formula uses the ordinary transpose and dot product. -/
theorem rowPinv_real (A : Matrix (Fin 1) n ℝ) :
    rowPinv A = (A 0 ⬝ᵥ A 0)⁻¹ • Aᵀ := by
  simp [rowPinv, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Over the reals the column formula uses the ordinary transpose and dot product. -/
theorem colPinv_real (A : Matrix n (Fin 1) ℝ) :
    colPinv A = ((fun i => A i 0) ⬝ᵥ (fun i => A i 0))⁻¹ • Aᵀ := by
  simp [colPinv, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem row_mul_conjTranspose (A : Matrix (Fin 1) n 𝕜) :
    A * Aᴴ = (star (A 0) ⬝ᵥ A 0) • (1 : Matrix (Fin 1) (Fin 1) 𝕜) := by
  ext i j
  obtain rfl := Subsingleton.elim i (0 : Fin 1)
  obtain rfl := Subsingleton.elim j (0 : Fin 1)
  simp [Matrix.mul_apply, dotProduct, mul_comm]

theorem row_dotProduct_ne_zero {A : Matrix (Fin 1) n 𝕜} (hA : A ≠ 0) :
    star (A 0) ⬝ᵥ A 0 ≠ 0 := by
  intro h
  have hv := dotProduct_star_self_eq_zero.mp h
  apply hA
  ext i j
  obtain rfl := Subsingleton.elim i (0 : Fin 1)
  exact congrFun hv j

/-- A nonzero row times its candidate pseudoinverse is the `1 × 1` identity. -/
theorem mul_rowPinv {A : Matrix (Fin 1) n 𝕜} (hA : A ≠ 0) :
    A * rowPinv A = 1 := by
  rw [rowPinv, Matrix.mul_smul, row_mul_conjTranspose, smul_smul,
    inv_mul_cancel₀ (row_dotProduct_ne_zero hA), one_smul]

/-- The row formula satisfies all four Penrose equations, including at zero. -/
theorem rowPinv_isMoorePenrose (A : Matrix (Fin 1) n 𝕜) :
    IsMoorePenrose A (rowPinv A) := by
  by_cases hA : A = 0
  · subst A
    simpa using (IsMoorePenrose.zero (m := Fin 1) (n := n) (𝕜 := 𝕜))
  constructor
  · rw [mul_rowPinv hA, Matrix.one_mul]
  · rw [Matrix.mul_assoc, mul_rowPinv hA, Matrix.mul_one]
  · rw [mul_rowPinv hA, Matrix.conjTranspose_one]
  · simp [rowPinv, Matrix.smul_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, dotProduct, mul_comm]

@[simp] theorem rowPinv_conjTranspose (A : Matrix n (Fin 1) 𝕜) :
    (rowPinv Aᴴ)ᴴ = colPinv A := by
  simp [rowPinv, colPinv, Matrix.conjTranspose_smul, dotProduct, mul_comm]

/-- The column formula satisfies all four Penrose equations, including at zero. -/
theorem colPinv_isMoorePenrose (A : Matrix n (Fin 1) 𝕜) :
    IsMoorePenrose A (colPinv A) := by
  simpa only [Matrix.conjTranspose_conjTranspose, rowPinv_conjTranspose] using
    (rowPinv_isMoorePenrose Aᴴ).conjTranspose

/-- The row formula is the unique Moore–Penrose pseudoinverse. -/
theorem isMoorePenrose_row_iff (A : Matrix (Fin 1) n 𝕜) (B : Matrix n (Fin 1) 𝕜) :
    IsMoorePenrose A B ↔ B = rowPinv A :=
  ⟨fun h => h.unique (rowPinv_isMoorePenrose A), fun h => h ▸ rowPinv_isMoorePenrose A⟩

/-- The column formula is the unique Moore–Penrose pseudoinverse. -/
theorem isMoorePenrose_col_iff (A : Matrix n (Fin 1) 𝕜) (B : Matrix (Fin 1) n 𝕜) :
    IsMoorePenrose A B ↔ B = colPinv A :=
  ⟨fun h => h.unique (colPinv_isMoorePenrose A), fun h => h ▸ colPinv_isMoorePenrose A⟩

/-- The usual piecewise formula, with the zero case separate from division. -/
theorem rowPinv_eq_if (A : Matrix (Fin 1) n 𝕜) :
    rowPinv A = if A = 0 then 0
      else (star (A 0) ⬝ᵥ A 0)⁻¹ • Aᴴ := by
  classical
  by_cases hA : A = 0
  · simp [hA]
  · simp [hA, rowPinv]

/-- The usual piecewise column formula, with the zero case separate from division. -/
theorem colPinv_eq_if (A : Matrix n (Fin 1) 𝕜) :
    colPinv A = if A = 0 then 0
      else (star (fun i => A i 0) ⬝ᵥ (fun i => A i 0))⁻¹ • Aᴴ := by
  classical
  by_cases hA : A = 0
  · simp [hA]
  · simp [hA, colPinv]

end Vectors

end SympyProofs.MoorePenrose
