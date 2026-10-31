module

public import SympyProofs.Sum.ShiftlessDecomposition.Algorithm
public import SympyProofs.Sum.ShiftlessDecomposition.Progress

/-!
Invariant of the degree-bounded square-free layer loop in `decompose`. Repeated exact division also computes maximal multiplicities
under the primitive contracts and input preconditions.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K]

open Polynomial

/-- The inline layer loop preserves the input as the product of the collected
layers and the remaining polynomial, with enough iterations left to finish. -/
structure LayerInvariant (p : Polynomial K) (processed : ℕ)
    (remaining : Polynomial K) (layers : Array (Polynomial K)) : Prop where
  monic : remaining.Monic
  degree_le : remaining.natDegree + processed ≤ p.natDegree
  reconstruct : layers.toList.prod * remaining = p
  layers_valid : ∀ b ∈ layers.toList, b.Monic ∧ Squarefree b
  nested : layers.toList.Pairwise (fun a b => b ∣ a)
  /-- This ensures that the next square-free layer divides each earlier layer. -/
  remaining_support : ∀ b ∈ layers.toList, remaining ∣ remaining.derivative * b

theorem LayerInvariant.initial {p : Polynomial K} (hp : p.Monic) :
    LayerInvariant p 0 p #[] := by
  exact ⟨hp, by simp, by simp, by simp, by simp, by simp⟩

theorem LayerInvariant.finish {p remaining : Polynomial K} {layers : Array (Polynomial K)}
    (h : LayerInvariant p p.natDegree remaining layers) :
    layers.toList.prod = p ∧ ∀ b ∈ layers.toList, b.Monic ∧ Squarefree b := by
  have hd : remaining.natDegree = 0 := by have := h.degree_le; omega
  have hr : remaining = 1 := h.monic.natDegree_eq_zero.mp hd
  exact ⟨by simpa [hr] using h.reconstruct, h.layers_valid⟩

theorem LayerInvariant.stop {p remaining : Polynomial K} {n : ℕ}
    {layers : Array (Polynomial K)} (h : LayerInvariant p n remaining layers)
    (hr : remaining = 1) : LayerInvariant p p.natDegree remaining layers :=
  ⟨h.monic, by simp [hr], h.reconstruct, h.layers_valid, h.nested, h.remaining_support⟩

variable [DecidableEq K]

theorem LayerInvariant.step [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {p remaining : Polynomial K} {n : ℕ} {layers : Array (Polynomial K)}
    (h : LayerInvariant p n remaining layers) (hne : remaining ≠ 1) :
    LayerInvariant p (n + 1) (remaining / ops.squarefreePart remaining)
      (layers.push (ops.squarefreePart remaining)) := by
  have hdiv : ∀ b ∈ layers.toList, ops.squarefreePart remaining ∣ b := fun b hb =>
    hops.squarefreePart_dvd_of_dvd_derivative_mul h.monic.ne_zero (h.remaining_support b hb)
  have hnext := hops.squarefree_next_dvd_derivative_mul h.monic.ne_zero
  refine ⟨hops.squarefree_next_monic h.monic, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hops.squarefree_next_degree_lt h.monic hne
    have hb := h.degree_le
    omega
  · simpa only [Array.toList_push, List.prod_append, List.prod_singleton, mul_assoc,
      (hops.squarefreeStep_reconstruct remaining h.monic.ne_zero).2] using h.reconstruct
  · intro b hb
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact h.layers_valid b hb
    · exact ⟨hops.squarefreePart_monic h.monic, hops.squarefreePart_squarefree h.monic.ne_zero⟩
  · simpa only [Array.toList_push, List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq, true_and] using And.intro h.nested hdiv
  · intro b hb
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hnext.trans (mul_dvd_mul_left _ (hdiv b hb))
    · exact hnext

/-- Repeated division with a remaining step bound. `multiplicity` supplies the bound. -/
def multiplicityAux (b : Polynomial K) : ℕ → Polynomial K → ℕ
  | 0, _ => 0
  | n + 1, p =>
    if p % b = 0 then
      multiplicityAux b n (p / b) + 1
    else 0

/-- Count exact divisions, with one final remainder test after at most
`p.natDegree` successful divisions by a nonconstant polynomial. -/
def multiplicity (p b : Polynomial K) : ℕ :=
  multiplicityAux b (p.natDegree + 1) p

private theorem multiplicityAux_spec
    (n : ℕ) (p b : Polynomial K) (hp : p ≠ 0) (hb : 0 < b.natDegree)
    (hn : p.natDegree < n) :
    let m := multiplicityAux b n p
    b ^ m ∣ p ∧ ¬b ^ (m + 1) ∣ p := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    rw [multiplicityAux]
    split
    · rename_i hr
      have hnext := exact_quotient_degree_lt hp hb hr
      have ih := ih (p / b) (exact_quotient_ne_zero hp hb0 hr) (by omega)
      have he := exact_division p b hb0 hr
      dsimp only at ih ⊢
      generalize multiplicityAux b n (p / b) = m at ih ⊢
      rw [← he, pow_succ', mul_dvd_mul_iff_left hb0]
      refine ⟨ih.1, ?_⟩
      simpa only [pow_succ' b (_ + 1), mul_dvd_mul_iff_left hb0] using ih.2
    · rename_i hr
      simp only [pow_zero, one_dvd, zero_add, pow_one, true_and]
      intro hd
      apply hr
      exact EuclideanDomain.mod_eq_zero.mpr hd

theorem multiplicity_spec (p b : Polynomial K)
    (hp : p ≠ 0) (hb : 0 < b.natDegree) :
    let n := multiplicity p b
    b ^ n ∣ p ∧ ¬b ^ (n + 1) ∣ p :=
  multiplicityAux_spec (p.natDegree + 1) p b hp hb (by omega)

end Gosper.ShiftlessDecomposition
