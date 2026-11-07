module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.LocalLogarithm
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# The half-open logarithm theorem for endomorphisms

The scalar convention `-π < im (log z) ≤ π` extends the logarithm to every
invertible complex endomorphism, including those with negative real eigenvalues.
The proof uses the same local polynomials and primary decomposition as the
open-strip theorem. No diagonalizability assumption is required.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

/-- The logarithm's imaginary part includes `π` and excludes `-π`. -/
def halfOpenStrip : Set ℂ := {z | -Real.pi < z.im ∧ z.im ≤ Real.pi}

@[simp] theorem mem_halfOpenStrip {z : ℂ} :
    z ∈ halfOpenStrip ↔ -Real.pi < z.im ∧ z.im ≤ Real.pi := Iff.rfl

theorem log_mem_halfOpenStrip (z : ℂ) : Complex.log z ∈ halfOpenStrip :=
  ⟨Complex.neg_pi_lt_log_im z, Complex.log_im_le_pi z⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Spectrum

variable [FiniteDimensional ℂ V]

/-- Interpolation maps each eigenvalue to its chosen scalar logarithm. -/
theorem spectrum_logInterpolation (f : End ℂ V) (d : ℕ) (hd : d ≠ 0) (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ f, (X - C z) ^ d ∣ p - localLogPolynomial z d) :
    spectrum ℂ (aeval f p) = Complex.log '' spectrum ℂ f := by
  nontriviality V
  rw [spectrum.map_polynomial_aeval_of_nonempty _ _
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ f)]
  apply Set.image_congr
  intro z hz
  obtain ⟨q, hq⟩ := hp z hz
  have h := congrArg (Polynomial.eval z) hq
  simpa [hd, localLogPolynomial_eval, sub_eq_zero] using h

theorem logInterpolation_spectrum_halfOpen (f : End ℂ V) (d : ℕ) (hd : d ≠ 0)
    (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ f, (X - C z) ^ d ∣ p - localLogPolynomial z d) :
    spectrum ℂ (aeval f p) ⊆ halfOpenStrip := by
  rw [spectrum_logInterpolation f d hd p hp]
  rintro _ ⟨z, _, rfl⟩
  exact log_mem_halfOpenStrip z

end Spectrum

section LogarithmInverses

variable [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem endExp_logInterpolation_of_nonzero (f : End ℂ V) (d : ℕ) (hd : Module.finrank ℂ V ≤ d)
    (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ f, (X - C z) ^ d ∣ p - localLogPolynomial z d)
    (hf : ∀ z ∈ spectrum ℂ f, z ≠ 0) : endExp (aeval f p) = f := by
  apply end_eq_on_primary f
  intro z hz x hx
  let u := (f.maxGenEigenspace z).subtype
  let g := primaryEnd f z
  have hn : (g - z • 1) ^ d = 0 :=
    pow_eq_zero_of_le ((Submodule.finrank_le _).trans hd)
      (nilpotent_pow_finrank (primaryEnd_nilpotent f z))
  have he : endExp (aeval g p) = g := by
    rw [aeval_eq_of_dvd_sub g z d (hp z hz)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hn)]
    exact endExp_localLogPolynomial g z d (hf z hz) hn
  have hi := endExp_intertwine u (aeval_intertwine u (primaryEnd_intertwine f z) p)
  have hi' := congrArg (fun t => t (⟨x, hx⟩ : f.maxGenEigenspace z)) hi
  change endExp (aeval f p) x = u (endExp (aeval g p) ⟨x, hx⟩) at hi'
  rw [he] at hi'
  exact hi'

theorem logInterpolation_endExp_halfOpen (l : End ℂ V) (d : ℕ) (hd : Module.finrank ℂ V ≤ d)
    (p : ℂ[X])
    (hp : ∀ z ∈ spectrum ℂ (endExp l), (X - C z) ^ d ∣ p - localLogPolynomial z d)
    (hl : spectrum ℂ l ⊆ halfOpenStrip) : aeval (endExp l) p = l := by
  apply end_eq_on_primary l
  intro z hz x hx
  let u := (l.maxGenEigenspace z).subtype
  let g := primaryEnd l z
  have hn : IsNilpotent (g - z • 1) := primaryEnd_nilpotent l z
  have hne : IsNilpotent (endExp g - Complex.exp z • 1) := by
    rw [endExp_sub_scalar g z hn]
    exact hn.isNilpotent_exp_sub_one.smul _
  have hpow : (endExp g - Complex.exp z • 1) ^ d = 0 :=
    pow_eq_zero_of_le ((Submodule.finrank_le _).trans hd) (nilpotent_pow_finrank hne)
  have he : aeval (endExp g) p = g := by
    rw [aeval_eq_of_dvd_sub (endExp g) (Complex.exp z) d (hp _ (mem_spectrum_endExp l hz))
      (by simpa [Algebra.algebraMap_eq_smul_one] using hpow)]
    exact localLogPolynomial_endExp_of_le g z d hn hpow (hl hz).1 (hl hz).2
  have hi := aeval_intertwine u (endExp_intertwine u (primaryEnd_intertwine l z)) p
  have hi' := congrArg (fun t => t (⟨x, hx⟩ : l.maxGenEigenspace z)) hi
  change aeval (endExp l) p x = u (aeval (endExp g) p ⟨x, hx⟩) at hi'
  rw [he] at hi'
  exact hi'

/-- Every invertible complex endomorphism has exactly one logarithm with
spectrum in the half-open strip `-π < im z ≤ π`. -/
theorem existsUnique_endHalfOpenLogarithm (f : End ℂ V) (hf : IsUnit f) :
    ∃! l : End ℂ V, endExp l = f ∧ spectrum ℂ l ⊆ halfOpenStrip := by
  obtain ⟨p, hp⟩ := exists_logInterpolation f.finite_spectrum (Module.finrank ℂ V + 1)
  have hnonzero : ∀ z ∈ spectrum ℂ f, z ≠ 0 := by
    intro z hz hz0
    subst z
    exact spectrum.zero_notMem ℂ hf hz
  refine ⟨aeval f p, ⟨endExp_logInterpolation_of_nonzero f _ (Nat.le_succ _) p hp hnonzero,
    logInterpolation_spectrum_halfOpen f _ (Nat.succ_ne_zero _) p hp⟩, ?_⟩
  intro l hl
  have h := logInterpolation_endExp_halfOpen l _ (Nat.le_succ _) p (by rwa [hl.1]) hl.2
  rw [hl.1] at h
  exact h.symm

end LogarithmInverses

end SympyProofs.MatrixExponential
