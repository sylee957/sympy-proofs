import SympyProofs.JordanKrylov.Mathematics.MinimalAnnihilatingPolynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.GCDMonoid.Finset

/-! # Matrix minimal polynomial from the annihilators of a basis -/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- The paper's `𝓟`: the minimal annihilating polynomials of the basis vectors. -/
noncomputable def basisAnnihilatingPolynomials (K : Subfield ℂ) {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) K) (e : Module.Basis ι K (Fin n → K)) : Set K[X] :=
  Set.range (fun i => minimalAnnihilatingPolynomial K A (e i))

/-- Every vector's minimal annihilating polynomial divides the matrix minimal polynomial. -/
theorem minimalAnnihilatingPolynomial_dvd_minpoly (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    minimalAnnihilatingPolynomial K A u ∣ minpoly K A := by
  apply (minimalAnnihilatingPolynomial_dvd_iff K A u _).mpr
  simp [minpoly.aeval]

/-- An annihilator of a spanning family annihilates the whole matrix. -/
theorem minpoly_dvd_iff_spanning_annihilators_dvd (K : Subfield ℂ) {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) K) (e : ι → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤) (p : K[X]) :
    minpoly K A ∣ p ↔ ∀ i, minimalAnnihilatingPolynomial K A (e i) ∣ p := by
  constructor
  · intro h i
    exact (minimalAnnihilatingPolynomial_dvd_minpoly K A (e i)).trans h
  · intro h
    apply minpoly.dvd K A
    have hk : Submodule.span K (Set.range e) ≤ LinearMap.ker (aeval A p).mulVecLin := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (minimalAnnihilatingPolynomial_dvd_iff K A (e i) p).mp (h i)
    rw [he] at hk
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simpa using hk (Submodule.mem_top : v ∈ (⊤ : Submodule K (Fin n → K)))

/-- A polynomial kills the matrix exactly when it kills every basis vector. -/
theorem minpoly_dvd_iff_basis_annihilators_dvd (K : Subfield ℂ) {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) K) (e : Module.Basis ι K (Fin n → K)) (p : K[X]) :
    minpoly K A ∣ p ↔ ∀ i, minimalAnnihilatingPolynomial K A (e i) ∣ p := by
  constructor
  · intro h i
    exact (minimalAnnihilatingPolynomial_dvd_minpoly K A (e i)).trans h
  · intro h
    apply minpoly.dvd K A
    have he : (aeval A p).mulVecLin = 0 := e.ext (fun i => by
      exact (minimalAnnihilatingPolynomial_dvd_iff K A (e i) p).mp (h i))
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simpa using LinearMap.congr_fun he v

/-- The matrix minimal polynomial is the monic least common multiple of the
minimal annihilating polynomials of any basis. -/
theorem minpoly_eq_lcm_basis_annihilators (K : Subfield ℂ) {n : ℕ}
    {ι : Type*} [Fintype ι] (A : Matrix (Fin n) (Fin n) K)
    (e : Module.Basis ι K (Fin n → K)) :
    minpoly K A = Finset.univ.lcm (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  classical
  have h₁ : minpoly K A ∣ Finset.univ.lcm
      (fun i => minimalAnnihilatingPolynomial K A (e i)) :=
    (minpoly_dvd_iff_basis_annihilators_dvd K A e _).mpr
      (fun i => Finset.dvd_lcm (Finset.mem_univ i))
  have h₂ : Finset.univ.lcm (fun i => minimalAnnihilatingPolynomial K A (e i)) ∣
      minpoly K A := Finset.lcm_dvd (fun i _ =>
    minimalAnnihilatingPolynomial_dvd_minpoly K A (e i))
  have hmon := minpoly.monic (Matrix.isIntegral A)
  have hn := normalize_eq_normalize h₁ h₂
  simpa only [hmon.normalize_eq_self, Finset.normalize_lcm] using hn

end SympyProofs.JordanKrylov
