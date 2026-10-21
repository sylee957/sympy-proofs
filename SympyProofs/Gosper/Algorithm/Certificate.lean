module

public import SympyProofs.Gosper.Algorithm.Polynomial

/-! Direct polynomial certificate checking over the coefficient field. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K]

local instance certificateDecidableEq : DecidableEq K := Classical.decEq K

/-- Cross-multiplied forward Gosper equation for the multiplier U/V. -/
def residual (P Q U V : K[X]) : K[X] :=
  P * taylor 1 U * V - Q * U * taylor 1 V - Q * V * taylor 1 V

/-- Equality in K[X] replaces the former rational sampling test. -/
def verify (P Q U V : K[X]) : Bool :=
  decide (Q ≠ 0 ∧ V ≠ 0 ∧ residual P Q U V = 0)

theorem verify_iff (P Q U V : K[X]) :
    verify P Q U V = true ↔ Q ≠ 0 ∧ V ≠ 0 ∧ residual P Q U V = 0 := by
  simp [verify]

theorem verify_sound (P Q U V : K[X]) (h : verify P Q U V = true) :
    Q ≠ 0 ∧ V ≠ 0 ∧ residual P Q U V = 0 := (verify_iff P Q U V).mp h

/-- Cancelling a common polynomial factor preserves the certificate identity. -/
theorem verify_cancel_common (P Q U V d : K[X]) (hd : d ≠ 0)
    (h : verify P Q (d * U) (d * V) = true) : verify P Q U V = true := by
  obtain ⟨hQ, hV, he⟩ := verify_sound _ _ _ _ h
  rw [verify_iff]
  refine ⟨hQ, (mul_ne_zero_iff.mp hV).2, ?_⟩
  have hi : residual P Q (d * U) (d * V) =
      (d * taylor 1 d) * residual P Q U V := by
    simp only [residual, taylor_mul]
    ring
  rw [hi] at he
  exact (mul_eq_zero.mp he).resolve_left
    (mul_ne_zero hd ((taylor_eq_zero 1 d).not.mpr hd))

theorem verify_div_gcd (P Q U V : K[X]) (h : verify P Q U V = true) :
    verify P Q (U / gcd U V) (V / gcd U V) = true := by
  have hd : gcd U V ≠ 0 := gcd_ne_zero_of_right (verify_sound P Q U V h).2.1
  apply verify_cancel_common _ _ _ _ _ hd
  simpa only [EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left U V),
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right U V)] using h

end Gosper.Algorithm
