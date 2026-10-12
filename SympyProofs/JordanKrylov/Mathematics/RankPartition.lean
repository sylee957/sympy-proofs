import SympyProofs.JordanKrylov.Mathematics.VectorRank

/-! # Partition of a set of primary vectors by rank -/
namespace SympyProofs.JordanKrylov

/-- The paper's S^(ℓ): the vectors in S of f-rank ℓ. -/
def rankSubset (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K)
    (S : Set (Fin n → K)) (ℓ : ℕ) : Set (Fin n → K) :=
  {u ∈ S | vectorRank K A f u = ℓ}

@[simp] theorem mem_rankSubset (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K)
    (S : Set (Fin n → K)) (ℓ : ℕ) (u : Fin n → K) :
    u ∈ rankSubset K A f S ℓ ↔ u ∈ S ∧ vectorRank K A f u = ℓ := Iff.rfl

theorem rankSubset_finite (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K)
    (S : Set (Fin n → K)) (hS : S.Finite) (ℓ : ℕ) :
    (rankSubset K A f S ℓ).Finite := hS.subset (fun _ h => h.1)

/-- The nonzero vectors in a primary power kernel are partitioned by ranks 1,…,ℓbar.
The union identity also holds for infinite subsets. -/
theorem eq_iUnion_rankSubset (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K)
    (S : Set (Fin n → K)) (ℓbar : ℕ)
    (hS : S ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (hzero : (0 : Fin n → K) ∉ S) :
    S = ⋃ ℓ ∈ Set.Icc 1 ℓbar, rankSubset K A f S ℓ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_Icc, mem_rankSubset]
  constructor
  · intro hu
    have hu0 : u ≠ 0 := by rintro rfl; exact hzero hu
    exact ⟨vectorRank K A f u, vectorRank_bounds K A f u hu0 (hS hu), hu, rfl⟩
  · rintro ⟨ℓ, _, hu, _⟩
    exact hu

/-- Different ranks give disjoint subsets. -/
theorem rankSubset_disjoint (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K)
    (S : Set (Fin n → K)) {ℓ k : ℕ} (hne : ℓ ≠ k) :
    Disjoint (rankSubset K A f S ℓ) (rankSubset K A f S k) := by
  rw [Set.disjoint_left]
  intro u hu hv
  exact hne (hu.2.symm.trans hv.2)

end SympyProofs.JordanKrylov
