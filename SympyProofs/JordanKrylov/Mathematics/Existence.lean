import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Existence of the base-field vector in Section 2

Tajima, Ohara, Terui, arXiv:2209.04807v5, before Lemma 1.
Only a subfield of ℂ is required. No computability, monicity, or
irreducibility assumptions are needed for this existence result.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

private theorem map_matrix_aeval {R S : Type*} [CommSemiring R] [CommSemiring S]
    {n : ℕ} (φ : R →+* S) (A : Matrix (Fin n) (Fin n) R) (f : R[X]) :
    (aeval A f).map φ = aeval (A.map φ) (f.map φ) := by
  refine map_aeval_eq_aeval_map (φ := φ)
    (ψ := (φ.mapMatrix : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) S)) ?_ f A
  ext x i j
  by_cases h : i = j <;>
    simp [algebraMap, Matrix.scalar, Matrix.diagonal, Matrix.map_apply, h]

/-- A nonconstant factor of the characteristic polynomial annihilates a nonzero
vector over the original subfield K. -/
theorem exists_nonzero_annihilated (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (hdegree : 0 < f.natDegree) (hfactor : f ∣ A.charpoly) :
    ∃ w : Fin n → K, w ≠ 0 ∧ (aeval A f) *ᵥ w = 0 := by
  let B := A.map K.subtype
  let g := f.map K.subtype
  have hgdegree : 0 < g.degree := by
    simpa [g] using (natDegree_pos_iff_degree_pos.mp hdegree)
  obtain ⟨a, ha⟩ := Complex.exists_root hgdegree
  have hgdiv : g ∣ B.charpoly := by
    rw [Matrix.charpoly_map]
    exact Polynomial.map_dvd K.subtype hfactor
  have hchar : B.charpoly.eval a = 0 := by
    obtain ⟨q, hq⟩ := hgdiv
    rw [hq, eval_mul, ha.eq_zero, zero_mul]
  have hdet : (Matrix.scalar (Fin n) a - B).det = 0 := by
    rwa [Matrix.eval_charpoly] at hchar
  obtain ⟨v, hv, hvec⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hx : (aeval B (X - C a)) *ᵥ v = 0 := by
    have heig : B *ᵥ v = a • v := by
      have hs : Matrix.scalar (Fin n) a = a • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, h]
      rw [hs, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hvec
      exact (sub_eq_zero.mp hvec).symm
    simp [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, heig]
  have hgv : (aeval B g) *ᵥ v = 0 := by
    obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr ha)
    rw [hq, mul_comm (X - C a), map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hdetC : (aeval B g).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hgv⟩
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  apply K.subtype.injective
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, map_matrix_aeval]
  exact hdetC

end SympyProofs.JordanKrylov
