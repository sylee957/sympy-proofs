module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Saturation
public import SympyProofs.Calculus.Antiderivative.Extension.SimplePole

/-! The necessary simple-pole and special-generator tests for saturated logarithms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial Extension.SimplePole
open scoped Polynomial

variable {F : Type*} [Field F] [CharZero F]
local notation "ι" => algebraMap F[X] (RatFunc F)

/-- A saturated logarithmic derivative has at most simple poles. -/
theorem simple_of_saturated (δ : Derivation ℤ F[X] F[X]) (D : Model.Der (RatFunc F))
    (hmap : ∀ p, D (ι p) = ι (δ p)) {w : RatFunc F} (h : Saturated D w) : Simple w := by
  obtain ⟨m, y, hm, hy, he⟩ := h
  have yn := RatFunc.num_ne_zero hy
  have yd := y.denom_ne_zero
  have hlog := (simple_logDeriv δ yn).sub (simple_logDeriv δ yd)
  have eq : D y / y = ι (δ y.num) / ι y.num - ι (δ y.denom) / ι y.denom := by
    conv_lhs => rw [← y.num_div_denom]
    rw [Extension.logDeriv_div (RatFunc.algebraMap_ne_zero yn) (RatFunc.algebraMap_ne_zero yd),
      hmap, hmap]
  rw [← eq, he] at hlog
  have hscale := hlog.C_mul ((m : F)⁻¹)
  simpa [mul_assoc, ← mul_assoc, Nat.ne_of_gt hm] using hscale

/-- A saturated logarithmic derivative has no pole at a generator dividing its own derivative. -/
theorem integral_of_saturated (δ : Derivation ℤ F[X] F[X])
    (D : Model.Der (RatFunc F)) (hmap : ∀ p, D (ι p) = ι (δ p))
    {b : F[X]} (hx : δ X = b * X) {w : RatFunc F} (h : Saturated D w) : Integral X w := by
  obtain ⟨m, y, hm, hy, he⟩ := h
  have yn := RatFunc.num_ne_zero hy
  have yd := y.denom_ne_zero
  have hlog := (integral_X_logDeriv δ hx yn).sub prime_X (integral_X_logDeriv δ hx yd)
  have eq : D y / y = ι (δ y.num) / ι y.num - ι (δ y.denom) / ι y.denom := by
    conv_lhs => rw [← y.num_div_denom]
    rw [Extension.logDeriv_div (RatFunc.algebraMap_ne_zero yn) (RatFunc.algebraMap_ne_zero yd),
      hmap, hmap]
  rw [← eq, he] at hlog
  have hscale := (integral_algebraMap prime_X (C (m : F)⁻¹)).mul prime_X hlog
  rw [RatFunc.algebraMap_C] at hscale
  simpa [mul_assoc, ← mul_assoc, Nat.ne_of_gt hm] using hscale

end SympyProofs.Calculus.Antiderivative.Logarithmic
