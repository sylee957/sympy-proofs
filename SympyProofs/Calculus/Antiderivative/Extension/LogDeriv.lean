module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! The logarithmic derivative `D A / A` of a product, a power, an inverse and a quotient, for
any derivation `D` of a field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension

section Generic

variable {F : Type*} [Field F] {D : Derivation ℤ F F}

/-- The logarithmic derivative of a product is the sum of the logarithmic derivatives. -/
theorem logDeriv_mul {A B : F} (hA : A ≠ 0) (hB : B ≠ 0) :
    D (A * B) / (A * B) = D A / A + D B / B := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The logarithmic derivative of a power is a multiple of the logarithmic derivative. -/
theorem logDeriv_pow {A : F} (hA : A ≠ 0) : ∀ m : ℕ, D (A ^ m) / A ^ m = (m : F) * (D A / A)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, logDeriv_mul (pow_ne_zero m hA) hA, logDeriv_pow hA m]
    push_cast
    ring

/-- The logarithmic derivative of an inverse is the negative of the logarithmic derivative. -/
theorem logDeriv_inv {A : F} (hA : A ≠ 0) : D A⁻¹ / A⁻¹ = -(D A / A) := by
  rw [Derivation.leibniz_inv]
  simp only [smul_eq_mul]
  field_simp

/-- The logarithmic derivative of a quotient is the difference of the logarithmic
derivatives. -/
theorem logDeriv_div {A B : F} (hA : A ≠ 0) (hB : B ≠ 0) :
    D (A / B) / (A / B) = D A / A - D B / B := by
  have e : A / B = A * B⁻¹ := div_eq_mul_inv _ _
  rw [e, logDeriv_mul hA (inv_ne_zero hB), logDeriv_inv hB]
  ring

end Generic

end SympyProofs.Calculus.Antiderivative.Extension
