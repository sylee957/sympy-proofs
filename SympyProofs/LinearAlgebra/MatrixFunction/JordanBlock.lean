module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic

/-!
# Explicit Jordan blocks

The shift matrix has ones on the first superdiagonal. Its powers shift that
diagonal to the right, so the shift of size `m` has `m`th power zero.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

variable {R : Type*} [Ring R]

/-- The nilpotent part of a Jordan block, with ones on the superdiagonal. -/
def jordanShift (R : Type*) [Zero R] [One R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => if i.val + 1 = j.val then 1 else 0

/-- A Jordan block of size `m` with eigenvalue `a`. -/
def jordanBlock (a : R) (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  Matrix.diagonal (fun _ => a) + jordanShift R m

theorem jordanShift_pow_apply (m k : ℕ) (i j : Fin m) :
    (jordanShift R m ^ k) i j = if i.val + k = j.val then 1 else 0 := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases hi : i.val + 1 < m
    · let t : Fin m := ⟨i.val + 1, hi⟩
      rw [Finset.sum_eq_single t]
      · simp [jordanShift, t, ih, Nat.add_comm, Nat.add_left_comm]
      · intro b hb hbt
        have hne : i.val + 1 ≠ b.val := by
          intro h
          apply hbt
          apply Fin.ext
          exact h.symm
        simp [jordanShift, hne]
      · simp
    · have hj : i.val + (k + 1) ≠ j.val := by omega
      rw [ite_eq_right hj]
      apply Finset.sum_eq_zero
      intro b hb
      have hne : i.val + 1 ≠ b.val := by omega
      simp [jordanShift, hne]

theorem jordanShift_pow_size (m : ℕ) : jordanShift R m ^ m = 0 := by
  ext i j
  rw [jordanShift_pow_apply, ite_eq_right (by omega)]
  rfl

theorem jordanShift_isNilpotent (m : ℕ) : IsNilpotent (jordanShift R m) :=
  ⟨m, jordanShift_pow_size m⟩

end SympyProofs.MatrixExponential
