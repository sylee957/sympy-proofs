module

public import SympyProofs.LinearAlgebra.MatrixFunction.Interpolation
public import SympyProofs.LinearAlgebra.MatrixLogarithm.InvariantSubspaces
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Primary functional calculus

Glue a local polynomial at every eigenvalue and evaluate the interpolant.
Although the interpolating polynomial is chosen noncomputably, the resulting
endomorphism is uniquely determined by its restrictions to primary subspaces.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def primaryPolynomial (f : End ℂ V) (q : ℂ → ℂ[X]) : ℂ[X] :=
  (exists_primaryInterpolation f.finite_spectrum (Module.finrank ℂ V + 1) q).choose

theorem primaryPolynomial_spec (f : End ℂ V) (q : ℂ → ℂ[X])
    (a : ℂ) (ha : a ∈ spectrum ℂ f) :
    (X - C a) ^ (Module.finrank ℂ V + 1) ∣ primaryPolynomial f q - q a :=
  (exists_primaryInterpolation f.finite_spectrum (Module.finrank ℂ V + 1) q).choose_spec a ha

theorem primaryPolynomial_eval (f : End ℂ V) (q : ℂ → ℂ[X])
    (a : ℂ) (ha : a ∈ spectrum ℂ f) :
    (primaryPolynomial f q).eval a = (q a).eval a := by
  obtain ⟨r, hr⟩ := primaryPolynomial_spec f q a ha
  have h := congrArg (Polynomial.eval a) hr
  simpa [sub_eq_zero] using h

noncomputable def primaryFunction (f : End ℂ V) (q : ℂ → ℂ[X]) : End ℂ V :=
  aeval f (primaryPolynomial f q)

theorem primaryFunction_intertwine (f : End ℂ V) (q : ℂ → ℂ[X])
    (a : ℂ) (ha : a ∈ spectrum ℂ f) :
    primaryFunction f q ∘ₗ (f.maxGenEigenspace a).subtype =
      (f.maxGenEigenspace a).subtype ∘ₗ aeval (primaryEnd f a) (q a) := by
  rw [primaryFunction, aeval_intertwine _ (primaryEnd_intertwine f a)]
  congr 1
  apply aeval_eq_of_dvd_sub _ a _ (primaryPolynomial_spec f q a ha)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
      (nilpotent_pow_finrank (primaryEnd_nilpotent f a))

theorem primaryFunction_unique (f : End ℂ V) (q : ℂ → ℂ[X]) (g : End ℂ V)
    (hg : ∀ a ∈ spectrum ℂ f,
      g ∘ₗ (f.maxGenEigenspace a).subtype =
        (f.maxGenEigenspace a).subtype ∘ₗ aeval (primaryEnd f a) (q a)) :
    g = primaryFunction f q := by
  apply end_eq_on_primary f
  intro a ha x hx
  exact congrArg (fun t => t (⟨x, hx⟩ : f.maxGenEigenspace a))
    ((hg a ha).trans (primaryFunction_intertwine f q a ha).symm)

/-- Any interpolant with the required local residues gives the same function. -/
theorem primaryFunction_eq_aeval (f : End ℂ V) (q : ℂ → ℂ[X]) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ f,
      (X - C a) ^ (Module.finrank ℂ V + 1) ∣ p - q a) :
    primaryFunction f q = aeval f p := by
  symm
  apply primaryFunction_unique
  intro a ha
  rw [aeval_intertwine _ (primaryEnd_intertwine f a)]
  congr 1
  apply aeval_eq_of_dvd_sub _ a _ (hp a ha)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
      (nilpotent_pow_finrank (primaryEnd_nilpotent f a))

end SympyProofs.MatrixExponential
