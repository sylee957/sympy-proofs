module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.Star.Real

/-! Sylvester's criterion, with the empty leading minor included. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

def leading {n : ℕ} {R : Type*} (P : Matrix (Fin n) (Fin n) R)
    (k : Fin (n + 1)) : Matrix (Fin k.val) (Fin k.val) R :=
  P.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
    (Fin.castLE (Nat.le_of_lt_succ k.isLt))

lemma posDef_border {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (C : Matrix (Fin n) (Fin 1) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (hB : B.PosDef) (hd : 0 < (fromBlocks B C Cᴴ D).det) :
    (fromBlocks B C Cᴴ D).PosDef := by
  let := hB.isUnit.invertible
  let S := D - Cᴴ * B⁻¹ * C
  have hs : 0 < S 0 0 := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_fin_one] at hd
    exact pos_of_mul_pos_right hd hB.det_pos.le
  have hS : S.PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i
      fin_cases j
      rfl
    · intro x
      simpa [dotProduct, mulVec, pow_two, mul_assoc, mul_left_comm] using
        mul_nonneg hs.le (sq_nonneg (x 0))
  have hM := (PosDef.fromBlocks₁₁ C D hB).mpr hS
  exact hM.posDef_iff_det_ne_zero.mpr hd.ne'

theorem posDef_of_leading_pos {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsHermitian) (h : ∀ k, 0 < (leading P k).det) : P.PosDef := by
  induction n with
  | zero =>
    apply PosDef.of_dotProduct_mulVec_pos hP
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  | succ n ih =>
    let B := P.submatrix Fin.castSucc Fin.castSucc
    let C : Matrix (Fin n) (Fin 1) ℝ := fun i _ => P i.castSucc (Fin.last n)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => P (Fin.last n) (Fin.last n)
    have hB : B.PosDef := by
      apply ih B (hP.submatrix _)
      intro k
      exact h ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
    have hfull : 0 < P.det := by
      simpa [leading] using h ⟨n + 1, Nat.lt_succ_self _⟩
    have he : P.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks B C Cᴴ D := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · fin_cases j
        rfl
      · fin_cases i
        change P (Fin.last n) j.castSucc = P j.castSucc (Fin.last n)
        exact (congrArg (fun M => M (Fin.last n) j.castSucc) hP.eq).symm
      · fin_cases i
        fin_cases j
        rfl
    have hd : 0 < (fromBlocks B C Cᴴ D).det := by
      rw [← he, det_submatrix_equiv_self]
      exact hfull
    have hp := (posDef_border C D hB hd).submatrix finSumFinEquiv.symm.injective
    rw [← he] at hp
    convert hp using 1
    ext i j
    simp

theorem posDef_iff_leading_pos {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    P.PosDef ↔ P.IsHermitian ∧ ∀ k, 0 < (leading P k).det := by
  constructor
  · intro h
    exact ⟨h.isHermitian, fun k => (h.submatrix (Fin.castLE_injective _)).det_pos⟩
  · rintro ⟨hP, h⟩
    exact posDef_of_leading_pos P hP h

end SympyProofs.NeumannSeries
