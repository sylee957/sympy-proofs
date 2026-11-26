module

public import SympyProofs.Calculus.Antiderivative.Program.Step.Resultant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Ring

/-! Correctness of the Euclidean resultant against the Sylvester determinant. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

open Polynomial
open scoped Polynomial

variable {F : Type} [Field F]

/-- One Euclidean division lowers the formal degree and contributes a leading-coefficient power. -/
private theorem resultant_remainder (a b : F[X]) (hd : b.natDegree ≠ 0)
    (hle : b.natDegree ≤ a.natDegree) :
    a.resultant b = (-1 : F) ^ (a.natDegree * b.natDegree) *
      b.leadingCoeff ^ (a.natDegree - (a % b).natDegree) * b.resultant (a % b) := by
  classical
  have hb : b ≠ 0 := by rintro rfl; simp at hd
  have hr := Polynomial.natDegree_mod_lt a hd
  have hm := hr.le.trans hle
  have hi := EuclideanDomain.mod_add_div a b
  have hq : (a / b).natDegree + b.natDegree ≤ a.natDegree := by
    by_cases hz : a / b = 0
    · simpa [hz] using hle
    rw [← Polynomial.natDegree_mul hz hb, mul_comm, eq_sub_of_add_eq' hi]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le le_rfl hm)
  have hs := resultant_add_mul_right b (a % b) (a / b) b.natDegree a.natDegree hq le_rfl
  rw [hi] at hs
  have ht := resultant_add_right_deg b (a % b) b.natDegree (a % b).natDegree
    (a.natDegree - (a % b).natDegree) le_rfl
  rw [Nat.add_sub_of_le hm] at ht
  rw [resultant_comm, hs, ht, Polynomial.coeff_natDegree, mul_assoc]

variable [DecidableEq F]

/-- Enough fuel gives the determinant resultant at each pair in the remainder sequence. -/
private theorem resultantLoop_spec (fuel : ℕ) (a b : Poly F) (hd : b.natDegree ≤ a.natDegree)
    (hf : b.natDegree < fuel) :
    resultantLoop fuel a b = (Poly.equiv a).resultant (Poly.equiv b) := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
    rw [resultantLoop]
    by_cases h : b.natDegree = 0
    · simp [h]
    · have hr := Poly.natDegree_mod_lt a h
      simp only [ite_eq_right h]
      rw [ih _ _ hr.le (by omega)]
      rw [resultant_remainder (Poly.equiv a) (Poly.equiv b) (by simpa) (by simpa)]
      rw [← Poly.equiv_mod]
      simp only [Poly.natDegree_equiv, Poly.leadingCoeff_equiv]

/-- The executable resultant is Mathlib's determinant of the Sylvester matrix. -/
theorem resultant_spec (a b : Poly F) :
    resultant a b = (Poly.equiv a).resultant (Poly.equiv b) := by
  unfold resultant
  split
  · rename_i h
    rw [resultantLoop_spec _ _ _ h.le (by omega), resultant_comm (Poly.equiv a)]
    simp
  · rename_i h
    exact resultantLoop_spec _ _ _ (Nat.le_of_not_lt h) (by omega)

end SympyProofs.Calculus.Antiderivative.Step
