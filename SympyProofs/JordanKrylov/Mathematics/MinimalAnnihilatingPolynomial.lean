import SympyProofs.JordanKrylov.Mathematics.Existence
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Ideal.MonicSpan

/-!
# Minimal annihilating polynomials of vectors

Definition 7 of the Jordan–Krylov paper. The annihilator of u consists
of the polynomials h with h(A)u = 0. Its unique monic generator is π_(A,u).
This is the annihilator of a vector, not the annihilator of the whole matrix.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- Ann_{K[λ]}(u) = {h | h(A)u = 0}, as an ideal of K[λ]. -/
noncomputable def vectorAnnihilator (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) : Ideal K[X] :=
  Ideal.torsionOf K[X] (Module.AEval' A.mulVecLin)
    (Module.AEval'.of A.mulVecLin u)

@[simp] theorem mem_vectorAnnihilator (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (h : K[X]) :
    h ∈ vectorAnnihilator K A u ↔ (aeval A h) *ᵥ u = 0 := by
  change (aeval A.mulVecLin h) u = 0 ↔ (aeval A h) *ᵥ u = 0
  have heval := Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' A h
  change aeval A.mulVecLin h = Matrix.toLinAlgEquiv' (aeval A h) at heval
  rw [heval]
  rfl

/-- Cayley–Hamilton supplies a nonzero polynomial in the vector's annihilator. -/
theorem vectorAnnihilator_ne_bot (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    vectorAnnihilator K A u ≠ ⊥ := by
  intro hz
  have hmem : A.charpoly ∈ vectorAnnihilator K A u := by
    simp [Matrix.aeval_self_charpoly]
  rw [hz, Ideal.mem_bot] at hmem
  exact A.charpoly_monic.ne_zero hmem

private theorem exists_monic_vectorAnnihilator (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    ∃ q : K[X], q.Monic ∧ vectorAnnihilator K A u = Ideal.span {q} :=
  Polynomial.exists_monic_span _ (vectorAnnihilator_ne_bot K A u)

/-- π_(A,u): the monic generator of the ideal of polynomials annihilating u. -/
noncomputable def minimalAnnihilatingPolynomial (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) : K[X] :=
  Classical.choose (exists_monic_vectorAnnihilator K A u)

theorem minimalAnnihilatingPolynomial_monic (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    (minimalAnnihilatingPolynomial K A u).Monic :=
  (Classical.choose_spec (exists_monic_vectorAnnihilator K A u)).1

/-- The defining monic-generator property in Definition 7. -/
theorem vectorAnnihilator_eq_span (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    vectorAnnihilator K A u = Ideal.span {minimalAnnihilatingPolynomial K A u} :=
  (Classical.choose_spec (exists_monic_vectorAnnihilator K A u)).2

/-- A polynomial annihilates u exactly when it is a multiple of π_(A,u). -/
theorem minimalAnnihilatingPolynomial_dvd_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (h : K[X]) :
    minimalAnnihilatingPolynomial K A u ∣ h ↔ (aeval A h) *ᵥ u = 0 := by
  rw [← mem_vectorAnnihilator, vectorAnnihilator_eq_span, Ideal.mem_span_singleton]

/-- The defined polynomial is monic and divides exactly the polynomials
whose evaluation at A annihilates u. -/
theorem minimalAnnihilatingPolynomial_spec (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    (minimalAnnihilatingPolynomial K A u).Monic ∧
      ∀ h : K[X], minimalAnnihilatingPolynomial K A u ∣ h ↔
        (aeval A h) *ᵥ u = 0 :=
  ⟨minimalAnnihilatingPolynomial_monic K A u,
    minimalAnnihilatingPolynomial_dvd_iff K A u⟩

theorem minimalAnnihilatingPolynomial_annihilates (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    (aeval A (minimalAnnihilatingPolynomial K A u)) *ᵥ u = 0 :=
  (minimalAnnihilatingPolynomial_dvd_iff K A u _).mp dvd_rfl

/-- The monic generator is unique. -/
theorem minimalAnnihilatingPolynomial_unique (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (q : K[X])
    (hq : q.Monic) (hgen : vectorAnnihilator K A u = Ideal.span {q}) :
    q = minimalAnnihilatingPolynomial K A u := by
  have hqmem : q ∈ vectorAnnihilator K A u := by
    rw [hgen]
    exact Ideal.mem_span_singleton_self q
  have hp : minimalAnnihilatingPolynomial K A u ∈ vectorAnnihilator K A u := by
    rw [vectorAnnihilator_eq_span]
    exact Ideal.mem_span_singleton_self _
  rw [vectorAnnihilator_eq_span, Ideal.mem_span_singleton] at hqmem
  rw [hgen, Ideal.mem_span_singleton] at hp
  exact eq_of_monic_of_dvd_of_natDegree_le
    (minimalAnnihilatingPolynomial_monic K A u) hq hqmem
    (natDegree_le_of_dvd hp (minimalAnnihilatingPolynomial_monic K A u).ne_zero)

/-- Its degree is minimal among nonzero polynomials annihilating u. -/
theorem minimalAnnihilatingPolynomial_degree_le (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (h : K[X])
    (hh : h ≠ 0) (hhu : (aeval A h) *ᵥ u = 0) :
    (minimalAnnihilatingPolynomial K A u).degree ≤ h.degree :=
  degree_le_of_dvd ((minimalAnnihilatingPolynomial_dvd_iff K A u h).mpr hhu) hh

end SympyProofs.JordanKrylov
