module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Diagonalization by a specified basis matrix -/

@[expose] public section

namespace SympyProofs.Diagonalization

open Matrix

variable {n : ℕ} {K : Type*} [Field K]

/-- The returned basis is invertible and conjugates the given diagonal to A. -/
def IsDiagonalization (A P : Matrix (Fin n) (Fin n) K) (d : Fin n → K) : Prop :=
  P.det ≠ 0 ∧ A = P * diagonal d * P⁻¹

theorem isDiagonalization_iff (A P : Matrix (Fin n) (Fin n) K) (d : Fin n → K) :
    IsDiagonalization A P d ↔ P.det ≠ 0 ∧ A * P = P * diagonal d := by
  constructor
  · rintro ⟨hd, rfl⟩
    exact ⟨hd, by simp [mul_assoc, P.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hd)]⟩
  · rintro ⟨hd, he⟩
    exact ⟨hd, by rw [← he, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hd)]⟩

end SympyProofs.Diagonalization
