import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Moore–Penrose equations and uniqueness

The four defining equations, their compatibility with conjugate transpose,
and uniqueness of the pseudoinverse for finite real or complex matrices.
-/

namespace SympyProofs.MoorePenrose

open Matrix

section Penrose

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The four defining equations for a Moore–Penrose pseudoinverse. -/
structure IsMoorePenrose (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) : Prop where
  left : A * B * A = A
  right : B * A * B = B
  left_hermitian : (A * B)ᴴ = A * B
  right_hermitian : (B * A)ᴴ = B * A

namespace IsMoorePenrose

theorem zero : IsMoorePenrose (0 : Matrix m n 𝕜) 0 := by
  constructor <;> simp

/-- Taking conjugate transposes preserves the Penrose equations. -/
theorem conjTranspose {A : Matrix m n 𝕜} {B : Matrix n m 𝕜}
    (h : IsMoorePenrose A B) : IsMoorePenrose Aᴴ Bᴴ := by
  constructor
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose h.left
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose h.right
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      h.right_hermitian.symm
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      h.left_hermitian.symm

/-- The four equations determine at most one pseudoinverse. -/
theorem unique {A : Matrix m n 𝕜} {B C : Matrix n m 𝕜}
    (hB : IsMoorePenrose A B) (hC : IsMoorePenrose A C) : B = C := by
  have hleft : A * B = A * C := by
    calc
      A * B = (A * C) * (A * B) := by rw [← Matrix.mul_assoc, hC.left]
      _ = ((A * C) * (A * B))ᴴ := by
        rw [← Matrix.mul_assoc, hC.left, hB.left_hermitian]
      _ = (A * B) * (A * C) := by
        rw [Matrix.conjTranspose_mul, hB.left_hermitian, hC.left_hermitian]
      _ = A * C := by rw [← Matrix.mul_assoc, hB.left]
  have hright : B * A = C * A := by
    calc
      B * A = (B * A) * (C * A) := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A C A, hC.left]
      _ = ((B * A) * (C * A))ᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc A C A, hC.left, hB.right_hermitian]
      _ = (C * A) * (B * A) := by
        rw [Matrix.conjTranspose_mul, hC.right_hermitian, hB.right_hermitian]
      _ = C * A := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A B A, hB.left]
  calc
    B = B * A * B := hB.right.symm
    _ = C * A * B := by rw [hright]
    _ = C * (A * C) := by rw [Matrix.mul_assoc, hleft]
    _ = C := by rw [← Matrix.mul_assoc, hC.right]

end IsMoorePenrose

end Penrose

end SympyProofs.MoorePenrose
