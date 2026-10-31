module

public import SympyProofs.Sum.ShiftlessDecomposition.Layers

/-! The first square-free layer is the support of all extracted layers. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K]

open Polynomial

/-- The support contains precisely the factors of the layers. -/
structure SupportInvariant (layers : List (Polynomial K)) (S : Polynomial K) : Prop where
  monic : S.Monic
  squarefree : Squarefree S
  divides : ∀ p ∈ layers, p ∣ S
  dvd_prod : S ∣ layers.prod
  eq_one_or_mem : S = 1 ∨ S ∈ layers

/-- Nested layers have their first layer as support; the empty case has support one. -/
theorem LayerInvariant.support {p remaining : Polynomial K} {n : ℕ}
    {layers : Array (Polynomial K)} (h : LayerInvariant p n remaining layers) :
    SupportInvariant layers.toList (layers[0]?.getD 1) := by
  suffices hs : SupportInvariant layers.toList ((layers.toList[0]?).getD 1) by
    simpa only [Array.getElem?_toList] using hs
  generalize hl : layers.toList = ls
  have hv := hl ▸ h.layers_valid
  have hn := hl ▸ h.nested
  cases ls with
  | nil => exact ⟨monic_one, squarefree_one, by simp, by simp, by simp⟩
  | cons b bs =>
    obtain ⟨hm, hsq⟩ := hv b (by simp)
    refine ⟨hm, hsq, ?_, List.dvd_prod (by simp), by simp⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact dvd_rfl
    · exact (List.pairwise_cons.mp hn).1 a ha

/-- Completed layers of a nonconstant monic input have nontrivial support. -/
theorem LayerInvariant.support_ne_one {p remaining : Polynomial K}
    {layers : Array (Polynomial K)} (h : LayerInvariant p p.natDegree remaining layers)
    (hp : p ≠ 1) : layers[0]?.getD 1 ≠ 1 := by
  intro hS
  have hl : ∀ b ∈ layers.toList, b = 1 := by
    intro b hb
    apply (h.layers_valid b hb).1.eq_one_of_isUnit
    apply isUnit_of_dvd_one
    simpa [hS] using h.support.divides b hb
  exact hp (h.finish.1.symm.trans (List.prod_eq_one hl))

end Gosper.ShiftlessDecomposition
