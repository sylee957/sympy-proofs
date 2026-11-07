module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Endomorphism
public import SympyProofs.LinearAlgebra.MatrixLogarithm.Interpolation

/-!
# Logarithms on a generalized eigenspace

The logarithm of a scalar plus a nilpotent endomorphism is a finite polynomial.
Both inverse identities are proved here, before assembling the primary components.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section NilpotentLogarithm

variable [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem endExp_localLogPolynomial (f : End ℂ V) (z : ℂ) (d : ℕ)
    (hz : z ≠ 0) (hn : (f - z • 1) ^ d = 0) :
    endExp (aeval f (localLogPolynomial z d)) = f := by
  have hN : IsNilpotent (z⁻¹ • (f - z • 1)) :=
    (show IsNilpotent (f - z • 1) from ⟨d, hn⟩).smul z⁻¹
  rw [aeval_localLogPolynomial f z d (by simpa [Algebra.algebraMap_eq_smul_one] using hn),
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    endExp_scalar_add, endExp_eq_of_nilpotent (Nilpotent.isNilpotent_log hN),
    Nilpotent.exp_log hN, Complex.exp_log hz, smul_add, smul_smul,
    mul_inv_cancel₀ hz, one_smul, add_sub_cancel]

theorem endExp_sub_scalar (f : End ℂ V) (z : ℂ)
    (hn : IsNilpotent (f - z • 1)) :
    endExp f - Complex.exp z • 1 =
      Complex.exp z • (IsNilpotent.exp (f - z • 1) - 1) := by
  rw [endExp_eq_of_shift_nilpotent f z hn, smul_sub]

/-- The scalar inverse law includes the upper boundary `im z = π`. -/
theorem localLogPolynomial_endExp_of_le (f : End ℂ V) (z : ℂ) (d : ℕ)
    (hn : IsNilpotent (f - z • 1))
    (hd : (endExp f - Complex.exp z • 1) ^ d = 0)
    (hz₁ : -Real.pi < z.im) (hz₂ : z.im ≤ Real.pi) :
    aeval (endExp f) (localLogPolynomial (Complex.exp z) d) = f := by
  rw [aeval_localLogPolynomial _ _ _ (by simpa [Algebra.algebraMap_eq_smul_one] using hd),
    Complex.log_exp hz₁ hz₂, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, endExp_sub_scalar f z hn,
    smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero z), one_smul,
    Nilpotent.log_exp_sub_one hn, add_sub_cancel]

theorem localLogPolynomial_endExp (f : End ℂ V) (z : ℂ) (d : ℕ)
    (hn : IsNilpotent (f - z • 1))
    (hd : (endExp f - Complex.exp z • 1) ^ d = 0)
    (hz₁ : -Real.pi < z.im) (hz₂ : z.im < Real.pi) :
    aeval (endExp f) (localLogPolynomial (Complex.exp z) d) = f :=
  localLogPolynomial_endExp_of_le f z d hn hd hz₁ hz₂.le

end NilpotentLogarithm

end SympyProofs.MatrixExponential
