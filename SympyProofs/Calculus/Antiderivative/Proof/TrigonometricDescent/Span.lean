module

public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Descending a span by evaluating the two embeddings of a quadratic extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

/-- If a list of quadratic columns and its conjugate have the same span, separating their
real and imaginary parts produces precisely that span. -/
theorem span_parts {k V A B : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (xs : List A) (parts : A → B × B) (v : B → V) (j : k) (hj : j ≠ 0)
    (plus minus : A → V)
    (hp : ∀ x ∈ xs, plus x = v (parts x).1 + j • v (parts x).2)
    (hm : ∀ x ∈ xs, minus x = v (parts x).1 - j • v (parts x).2)
    (hs : Submodule.span k (plus '' {x | x ∈ xs}) = Submodule.span k (minus '' {x | x ∈ xs})) :
    Submodule.span k (v '' {x | x ∈ xs.flatMap (fun z => [(parts z).1, (parts z).2])}) =
      Submodule.span k (plus '' {x | x ∈ xs}) := by
  let U := Submodule.span k (plus '' {x | x ∈ xs})
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hx, xb⟩ := List.mem_flatMap.mp hb
    have p : plus x ∈ U := Submodule.subset_span ⟨x,hx,rfl⟩
    have m : minus x ∈ U := by
      rw [show U = _ from hs]
      exact Submodule.subset_span ⟨x,hx,rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at xb
    rcases xb with rfl | rfl
    · have eq : (2 : k)⁻¹ • (plus x + minus x) = v (parts x).1 := by
        rw [hp _ hx, hm _ hx]
        match_scalars <;> field_simp <;> ring
      exact eq ▸ U.smul_mem _ (U.add_mem p m)
    · have eq : (2*j)⁻¹ • (plus x - minus x) = v (parts x).2 := by
        rw [hp _ hx, hm _ hx]
        match_scalars <;> field_simp <;> ring
      exact eq ▸ U.smul_mem _ (U.sub_mem p m)
  · rintro _ ⟨x,hx,rfl⟩
    rw [hp x hx]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨_, List.mem_flatMap.mpr ⟨_,hx,List.mem_cons_self⟩,rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨_, List.mem_flatMap.mpr ⟨_,hx,by simp⟩,rfl⟩

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
