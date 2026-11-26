module

public import SympyProofs.Calculus.Antiderivative.Proof.Linear

/-! Column operations for parametric equations over arbitrary extensions of the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Linear

variable {k F V α β : Type} [Field k] [Field F] [AddCommGroup V] [Module k V]

/-- Send a coordinate vector to the corresponding constant-linear combination of columns. -/
noncomputable def accumulate (l : List α) (v : α → V) : (Fin l.length → k) →ₗ[k] V :=
  ∑ i : Fin l.length, (LinearMap.proj i).smulRight (v (l.get i))

@[simp] theorem accumulate_apply (l : List α) (v : α → V) (a : Fin l.length → k) :
    accumulate l v a = ∑ i : Fin l.length, a i • v (l.get i) := by simp [accumulate]

/-- The column span consists exactly of the coordinate combinations of these columns. -/
theorem mem_columns_iff (l : List α) (v : α → V) (y : V) :
    y ∈ Submodule.span k (v '' {c | c ∈ l}) ↔ ∃ a : Fin l.length → k, accumulate l v a = y := by
  classical
  change _ ↔ y ∈ LinearMap.range (accumulate l v)
  apply Iff.intro
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,hc,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hc
    exact ⟨Pi.single (⟨i,hi⟩ : Fin l.length) 1, by simp [accumulate_apply, Pi.single_apply]⟩
  · rintro ⟨a,rfl⟩
    rw [accumulate_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l.get i, List.get_mem _ _, rfl⟩)

/-- Applying a linear map to the computed kernel gives exactly its values on all solutions,
over the entire chosen extension field. -/
theorem mem_kernel_image_iff [DecidableEq F] (f : F →+* k) (rows : List (List F)) (m : ℕ)
    (T : (Fin m → k) →ₗ[k] V) (w : List F → β) (v : β → V)
    (he : ∀ q ∈ kernel rows m, v (w q) = T (vector f m q)) (y : V) :
    y ∈ Submodule.span k (v '' {b | b ∈ (kernel rows m).map w}) ↔
      ∃ a : Fin m → k, (∀ r ∈ rows, functional f m r a = 0) ∧ T a = y := by
  have eqn : v '' {b | b ∈ (kernel rows m).map w} =
      T '' (vector f m '' {q | q ∈ kernel rows m}) := by
    ext p
    constructor
    · rintro ⟨_,h,rfl⟩
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact ⟨_, ⟨q,hq,rfl⟩, (he q hq).symm⟩
    · rintro ⟨_, ⟨q,hq,rfl⟩, rfl⟩
      exact ⟨w q, List.mem_map_of_mem hq, he q hq⟩
  rw [eqn, ← Submodule.map_span]
  change (∃ a, a ∈ generated f rows m ∧ T a = y) ↔ _
  simp only [generated_iff]

/-- Mapping a list of directions through a linear transformation maps its entire span. -/
theorem mem_mapped_columns_iff {U : Type} [AddCommGroup U] [Module k U]
    (l : List α) (u : α → U) (w : α → β) (v : β → V) (T : U →ₗ[k] V)
    (he : ∀ c ∈ l, v (w c) = T (u c)) (y : V) :
    y ∈ Submodule.span k (v '' {b | b ∈ l.map w}) ↔
      ∃ x, x ∈ Submodule.span k (u '' {c | c ∈ l}) ∧ T x = y := by
  have eqn : v '' {b | b ∈ l.map w} = T '' (u '' {c | c ∈ l}) := by
    ext y
    constructor
    · rintro ⟨_,h,rfl⟩
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
      exact ⟨_, ⟨c,hc,rfl⟩, (he c hc).symm⟩
    · rintro ⟨_, ⟨c,hc,rfl⟩, rfl⟩
      exact ⟨w c, List.mem_map_of_mem hc, he c hc⟩
  rw [eqn, ← Submodule.map_span]
  rfl

end SympyProofs.Calculus.Antiderivative.Linear
