import SympyProofs.JordanKrylov.Mathematics.KrylovSpace
import Mathlib.Algebra.DirectSum.Module

/-! # Krylov generating sets

Definition 9 of the Jordan–Krylov paper. The sum is a submodule supremum;
the definition does not require the summands to be independent.
-/

namespace SympyProofs.JordanKrylov

/-- The generators in the positive layers of a rank-indexed family. -/
def algorithmInputSet {K : Type*} {n : ℕ} (V : ℕ → List (Fin n → K))
    (ℓbar : ℕ) : Set (Fin n → K) := {v | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ ℓbar ∧ v ∈ V ℓ}


/-- A set S generates W by taking the sum of the Krylov spaces of its vectors.
The condition S ⊆ W follows from this equality, since w ∈ L_A(w). -/
def IsKrylovGeneratingSet (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (S : Set (Fin n → K)) : Prop :=
  W = ⨆ w ∈ S, krylovSpace K A w

/-- Every generator belongs to the generated subspace. -/
theorem IsKrylovGeneratingSet.subset (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (S : Set (Fin n → K)) (h : IsKrylovGeneratingSet K A W S) :
    S ⊆ (W : Set (Fin n → K)) := by
  intro w hw
  rw [h]
  have hle : krylovSpace K A w ≤ ⨆ v ∈ S, krylovSpace K A v :=
    le_iSup_of_le w (le_iSup (fun _ : w ∈ S => krylovSpace K A w) hw)
  exact hle (self_mem_krylovSpace K A w)

/-- The empty set generates exactly the trivial vector space. -/
@[simp] theorem isKrylovGeneratingSet_empty_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) :
    IsKrylovGeneratingSet K A W ∅ ↔ W = ⊥ := by
  simp [IsKrylovGeneratingSet]

/-- The empty set is a Krylov generating set of {0}. -/
theorem empty_isKrylovGeneratingSet_bot (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    IsKrylovGeneratingSet K A ⊥ ∅ := by
  simp

end SympyProofs.JordanKrylov
