module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenEndomorphism

/-!
# The principal logarithm theorem for endomorphisms

Hermite interpolation constructs a logarithm on every primary component.
The same polynomial recovers any logarithm whose spectrum lies in the principal
strip, proving uniqueness without a diagonalizability assumption.

Take `d = dim V + 1`. The Chinese remainder theorem supplies a polynomial `p`
agreeing with the degree-`< d` logarithm expansion modulo `(X - λ)^d` at every
eigenvalue `λ` of `f`. Restricting to the generalized `λ`-eigenspace proves
`exp (p(f)) = f`; polynomial spectral mapping puts `p(f)` in the principal strip.
For any other strip-valued logarithm `l`, restrict to its generalized eigenspaces
and use `log (exp μ) = μ` and the nilpotent inverse identity to prove `p(exp l) = l`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

/-- The open strip selecting the principal branch of the logarithm. -/
def principalStrip : Set ℂ := {z | -Real.pi < z.im ∧ z.im < Real.pi}

theorem principalStrip_subset_halfOpenStrip : principalStrip ⊆ halfOpenStrip :=
  fun _ hz => ⟨hz.1, hz.2.le⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Spectrum

variable [FiniteDimensional ℂ V]

theorem logInterpolation_spectrum (f : End ℂ V) (d : ℕ) (hd : d ≠ 0) (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ f, (X - C z) ^ d ∣ p - localLogPolynomial z d)
    (hf : spectrum ℂ f ⊆ Complex.slitPlane) : spectrum ℂ (aeval f p) ⊆ principalStrip := by
  rw [spectrum_logInterpolation f d hd p hp]
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨Complex.neg_pi_lt_log_im z,
    lt_of_le_of_ne (Complex.log_im_le_pi z) (by
      simpa only [Complex.log_im] using Complex.slitPlane_arg_ne_pi (hf hz))⟩

end Spectrum

section LogarithmInverses

variable [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem endExp_logInterpolation (f : End ℂ V) (d : ℕ) (hd : Module.finrank ℂ V ≤ d)
    (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ f, (X - C z) ^ d ∣ p - localLogPolynomial z d)
    (hf : spectrum ℂ f ⊆ Complex.slitPlane) : endExp (aeval f p) = f :=
  endExp_logInterpolation_of_nonzero f d hd p hp
    (fun _ hz => Complex.slitPlane_ne_zero (hf hz))

theorem logInterpolation_endExp (l : End ℂ V) (d : ℕ) (hd : Module.finrank ℂ V ≤ d)
    (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ (endExp l), (X - C z) ^ d ∣ p - localLogPolynomial z d)
    (hl : spectrum ℂ l ⊆ principalStrip) : aeval (endExp l) p = l :=
  logInterpolation_endExp_halfOpen l d hd p hp (hl.trans principalStrip_subset_halfOpenStrip)

/-- Existence and uniqueness of the logarithm with spectrum in the open principal
strip, for every finite-dimensional complex endomorphism avoiding the branch cut. -/
theorem existsUnique_endLogarithm (f : End ℂ V)
    (hf : spectrum ℂ f ⊆ Complex.slitPlane) :
    ∃! l : End ℂ V, endExp l = f ∧ spectrum ℂ l ⊆ principalStrip := by
  obtain ⟨p, hp⟩ := exists_logInterpolation f.finite_spectrum (Module.finrank ℂ V + 1)
  refine ⟨aeval f p, ⟨endExp_logInterpolation f _ (Nat.le_succ _) p hp hf,
    logInterpolation_spectrum f _ (Nat.succ_ne_zero _) p hp hf⟩, ?_⟩
  intro l hl
  have h := logInterpolation_endExp l _ (Nat.le_succ _) p (by rwa [hl.1]) hl.2
  rw [hl.1] at h
  exact h.symm

end LogarithmInverses

end SympyProofs.MatrixExponential
