module

public import SympyProofs.Calculus.Antiderivative.Program.Constants.Parameters
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Quadratic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Analysis.Complex.Basic

/-! Evaluate formal constant parameters at an algebraically independent family of complex values. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {m : ℕ} (z : Fin m → ℂ) (h : AlgebraicIndependent ℚ z)

/-- Embed the rational function field in the specified complex constants. Algebraic independence
ensures that each nonzero polynomial denominator remains nonzero under evaluation. -/
noncomputable def Parameters.complexHom : Parameters m →+* ℂ :=
  (IsFractionRing.lift (A := MvPolynomial (Fin m) ℤ) (K := M ℤ m)
    (g := (MvPolynomial.aeval (R := ℤ) z).toRingHom)
    (algebraicIndependent_iff_injective_aeval.mp
      (h.restrictScalars (R := ℤ) (Int.cast_injective (α := ℚ))))).comp K.equiv.toRingHom

/-- Each coordinate parameter evaluates to the complex value supplied for that coordinate. -/
@[simp] theorem Parameters.complexHom_X (i : Fin m) :
    complexHom z h (K.ofPoly (MPoly.X i)) = z i := by
  simp [complexHom, IsFractionRing.lift_algebraMap]

/-- Extend evaluation of independent parameters by sending the formal imaginary unit to i. -/
noncomputable def WithI.parametersComplexHom : WithI (Parameters m) →+* ℂ := by
  letI := (Parameters.complexHom z h).toAlgebra
  exact (QuadraticAlgebra.lift ⟨Complex.I, by simp⟩).toRingHom

/-- The extension agrees with parameter evaluation on coefficients. -/
@[simp] theorem WithI.parametersComplexHom_C (a : Parameters m) :
    parametersComplexHom z h (QuadraticAlgebra.C a) = Parameters.complexHom z h a := by
  change Parameters.complexHom z h a * 1 + Parameters.complexHom z h 0 * Complex.I = _
  simp

/-- The formal imaginary unit evaluates to the analytic imaginary unit. -/
@[simp] theorem WithI.parametersComplexHom_imaginary :
    parametersComplexHom z h (imaginary (Parameters m)) = Complex.I := by
  change Parameters.complexHom z h 0 * 1 + Parameters.complexHom z h 1 * Complex.I = _
  simp

/-- For a single real constant, its transcendence over the rationals suffices for the
complex evaluation of rational functions in that constant and i. -/
theorem Parameters.independent_single_real (a : ℝ) (ha : Transcendental ℚ a) :
    AlgebraicIndependent ℚ (fun _ : Fin 1 => (a : ℂ)) :=
  (algebraicIndependent_singleton_iff 0).mpr
    ((transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective).mpr ha)

end SympyProofs.Calculus.Antiderivative
