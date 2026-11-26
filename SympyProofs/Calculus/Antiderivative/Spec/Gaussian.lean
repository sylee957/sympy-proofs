module

public import SympyProofs.Calculus.Antiderivative.Algebra.Gaussian
public import Mathlib.Analysis.Complex.Basic

/-! Interpret a Gaussian rational coefficient using the usual complex imaginary unit. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Gaussian

/-- The usual embedding sends the second basis element to the complex imaginary unit. -/
noncomputable def toComplex : Gaussian →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp⟩

/-- Gaussian constants have their usual values in the complex analytic model. -/
noncomputable instance : Algebra Gaussian ℂ := toComplex.toRingHom.toAlgebra

@[simp] theorem toComplex_I : toComplex I = Complex.I := by
  change (0 : ℚ) • (1 : ℂ) + (1 : ℚ) • Complex.I = _
  simp

end SympyProofs.Calculus.Antiderivative.Gaussian
