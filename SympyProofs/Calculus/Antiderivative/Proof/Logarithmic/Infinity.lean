module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Local

/-! The polynomial part of a saturated logarithmic derivative at infinity. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial Differential Extension.LiouvilleForm Extension.LiouvilleForm.AtInfinity
open scoped Polynomial

variable {F : Type*} [Field F] [CharZero F]
variable [Differential F] [Differential (RatFunc F)] [DifferentialAlgebra F (RatFunc F)]

/-- Removing the proper part at infinity leaves a saturated constant plus a rational
multiple of the linear generator velocity. -/
theorem infinity_of_saturated {a b : F}
    (dx : deriv (RatFunc.X : RatFunc F) = RatFunc.C a * RatFunc.X + RatFunc.C b)
    {w : RatFunc F} (h : Saturated deriv w) :
    ∃ (c : F) (r : ℚ), Saturated deriv c ∧ Proper (w - RatFunc.C (c + (r : F) * a)) := by
  obtain ⟨m, y, hm, hy, he⟩ := h
  let t := leadingRatio y
  have n0 : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have m0 : (m : RatFunc F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have t0 : t ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hy))
    (leadingCoeff_ne_zero.mpr y.denom_ne_zero)
  refine ⟨logDeriv t / m, (y.intDegree : ℚ) / m, ⟨m, t, hm, t0, ?_⟩, ?_⟩
  · change logDeriv t = _
    field_simp
  · have hp := proper_logDeriv dx y
    change Proper (logDeriv y - RatFunc.C (logDeriv t + (y.intDegree : F) * a)) at hp
    have hclear : logDeriv y = (m : RatFunc F) * w := he
    rw [hclear] at hp
    have hscale := hp.mul_bounded (bounded_C ((m : F)⁻¹))
    convert hscale using 1
    rw [map_add, map_add, map_mul, map_mul, map_div₀]
    push_cast
    simp only [map_inv₀, map_natCast, map_intCast, map_div₀]
    field_simp

omit [Differential F] [Differential (RatFunc F)] [DifferentialAlgebra F (RatFunc F)] in
/-- Comparing the proper parts at infinity determines the entire polynomial part. -/
theorem polynomial_part {A S : F[X]} (hS : S ≠ 0) (c : F)
    (h : Proper (algebraMap F[X] (RatFunc F) A / algebraMap _ _ S - RatFunc.C c)) :
    A / S = C c := by
  let j := algebraMap F[X] (RatFunc F)
  have hp := proper_div hS (Polynomial.degree_mod_lt A hS)
  have e : j A / j S = j (A / S) + j (A % S) / j S := by
    have h := congrArg j (EuclideanDomain.mod_add_div A S)
    rw [map_add, map_mul] at h
    field_simp [show j S ≠ 0 from RatFunc.algebraMap_ne_zero hS]
    linear_combination -h
  change Proper (j A / j S - RatFunc.C c) at h
  rw [e] at h
  have hh := h.sub hp
  have val : j (A / S - C c) = (j (A / S) + j (A % S) / j S - RatFunc.C c) - j (A % S) / j S := by
    rw [map_sub]
    change _ - RatFunc.C c = _
    ring
  exact sub_eq_zero.mp (proper_polynomial.mp (val ▸ hh))

end SympyProofs.Calculus.Antiderivative.Logarithmic
