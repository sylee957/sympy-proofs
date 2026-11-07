module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Invariant subspaces of complex endomorphisms

Polynomial evaluation preserves intertwining. Generalized eigenspaces provide
nilpotent restrictions and an extensionality principle in finite dimension.
These algebraic results require no norm or rational scalar structure.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

section PolynomialIntertwining

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem aeval_intertwine {f : End ℂ V} {g : End ℂ W} (u : V →ₗ[ℂ] W)
    (h : g ∘ₗ u = u ∘ₗ f) (p : Polynomial ℂ) :
    Polynomial.aeval g p ∘ₗ u = u ∘ₗ Polynomial.aeval f p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.smul_comp, LinearMap.comp_smul]
    exact congrArg (c • ·) (End.commute_pow_left_of_commute h k)

end PolynomialIntertwining

section GeneralizedEigenspaces

noncomputable def primaryEnd (f : End ℂ V) (z : ℂ) : End ℂ (f.maxGenEigenspace z) :=
  f.restrict (End.mapsTo_genEigenspace_of_comm (Commute.refl f) z ⊤)

theorem primaryEnd_intertwine (f : End ℂ V) (z : ℂ) :
    f ∘ₗ (f.maxGenEigenspace z).subtype =
      (f.maxGenEigenspace z).subtype ∘ₗ primaryEnd f z := rfl

variable [FiniteDimensional ℂ V]

theorem nilpotent_pow_finrank {f : End ℂ V} (hf : IsNilpotent f) :
    f ^ Module.finrank ℂ V = 0 := by
  obtain ⟨k, hk⟩ := hf
  ext x
  exact End.ker_pow_le_ker_pow_finrank f k (by simp [hk])

theorem primaryEnd_nilpotent (f : End ℂ V) (z : ℂ) :
    IsNilpotent (primaryEnd f z - z • 1) := by
  convert f.isNilpotent_restrict_genEigenspace_top z using 1
  ext x
  rfl

theorem end_eq_on_primary (f g h : End ℂ V)
    (heq : ∀ z ∈ spectrum ℂ f, ∀ x ∈ f.maxGenEigenspace z, g x = h x) : g = h := by
  have hker : (⊤ : Submodule ℂ V) ≤ (g - h).ker := by
    rw [← f.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro z
    by_cases hz : z ∈ spectrum ℂ f
    · intro x hx
      exact sub_eq_zero.mpr (heq z hz x hx)
    · have hb : f.maxGenEigenspace z = ⊥ := by
        by_contra hn
        exact hz ((show f.HasUnifEigenvalue z ⊤ from hn).lt zero_lt_one).mem_spectrum
      rw [hb]
      exact bot_le
  ext x
  exact sub_eq_zero.mp (hker (Submodule.mem_top))

end GeneralizedEigenspaces

end SympyProofs.MatrixExponential
