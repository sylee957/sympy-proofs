import SympyProofs.JordanKrylov.KrylovGeneratingSet

/-! # Jordan–Krylov independence and bases

Definitions 10 and 11. These are predicates on finite sets of vectors,
using mathlib's independence of submodules for the direct-sum condition.
Theorem 12 is proved in `SympyProofs.JordanKrylov.BasisExistence`;
its positive-rank uniqueness argument is in `RankMultiplicity`.
-/

namespace SympyProofs.JordanKrylov

open scoped DirectSum

/-- Definition 10: a finite set whose Krylov subspaces form an independent family. -/
def IsJordanKrylovIndependent (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (S : Set (Fin n → K)) : Prop :=
  S.Finite ∧ iSupIndep (fun w : S => krylovSpace K A w.val)

/-- Definition 11: a Jordan–Krylov independent generating set of W. -/
def IsJordanKrylovBasis (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (S : Set (Fin n → K)) : Prop :=
  IsKrylovGeneratingSet K A W S ∧ IsJordanKrylovIndependent K A S

/-- The empty set is Jordan–Krylov independent. -/
@[simp] theorem isJordanKrylovIndependent_empty (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : IsJordanKrylovIndependent K A ∅ := by
  refine ⟨Set.finite_empty, ?_⟩
  intro w
  exact False.elim w.property

/-- The empty set is a Jordan–Krylov basis exactly of the zero subspace. -/
@[simp] theorem isJordanKrylovBasis_empty_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) :
    IsJordanKrylovBasis K A W ∅ ↔ W = ⊥ := by
  simp [IsJordanKrylovBasis]

/-- The direct-sum formulation of a Jordan–Krylov basis. -/
theorem IsJordanKrylovBasis.nonempty_directSum_equiv (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (S : Set (Fin n → K)) (h : IsJordanKrylovBasis K A W S) :
    Nonempty ((⨁ w : S, krylovSpace K A w.val) ≃ₗ[K] W) := by
  classical
  have hspan : (⨆ w : S, krylovSpace K A w.val) = W := by
    simpa only [iSup_subtype] using h.1.symm
  exact ⟨(LinearEquiv.ofInjective (DirectSum.coeLinearMap _)
    h.2.2.dfinsupp_lsum_injective).trans
    (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap.trans hspan))⟩

/-- The zero vector generates the zero Krylov space. -/
@[simp] theorem krylovSpace_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : krylovSpace K A 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  simp [krylovVector]

/-- The literal definitions also allow {0} as a basis of {0}.
Thus uniqueness of rank counts must exclude rank zero or exclude zero generators. -/
theorem singleton_zero_isJordanKrylovBasis_bot (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    IsJordanKrylovBasis K A ⊥ {0} := by
  refine ⟨?_, Set.finite_singleton 0, ?_⟩
  · simp [IsKrylovGeneratingSet]
  · exact iSupIndep_subsingleton _

end SympyProofs.JordanKrylov
