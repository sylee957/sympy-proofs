module

public import SympyProofs.LinearAlgebra.Permanent.Basic
public import Mathlib.Data.Finset.Powerset

import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice

/-! Ryser's inclusion-exclusion formula for the permanent over a commutative ring.
Inclusion-exclusion removes the functions that miss a row. The remaining functions
are surjections of a finite type to itself, hence permutations. -/

@[expose] public section

namespace Matrix

open Finset

private theorem permanent_eq_sum_surjective {n R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.permanent = ∑ f ∈ univ.filter (Function.Surjective : (n → n) → Prop),
      ∏ j, A (f j) j := by
  classical
  unfold permanent
  apply sum_bij (fun (σ : Equiv.Perm n) _ => (σ : n → n))
  · intro σ _
    simp [σ.surjective]
  · intro σ _ τ _ h
    exact Equiv.ext (congrFun h)
  · intro f hf
    have hs : Function.Surjective f := (mem_filter.mp hf).2
    exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs, hs⟩,
      mem_univ _, rfl⟩
  · intro σ _
    rfl

/-- Ryser's formula in terms of column sums over subsets of rows. -/
theorem permanent_eq_sum_powerset_cols {n R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.permanent = ∑ s ∈ (univ : Finset n).powerset,
      (-1 : R) ^ (Fintype.card n - s.card) * ∏ j, ∑ i ∈ s, A i j := by
  classical
  let missing : n → Finset (n → n) := fun i => univ.filter (fun f => ∀ j, f j ≠ i)
  have hsurj : (univ.inf fun i => (missing i)ᶜ) =
      univ.filter (Function.Surjective : (n → n) → Prop) := by
    ext f
    simp [missing, mem_inf, Function.Surjective]
  have havoid (s : Finset n) : s.inf missing = Fintype.piFinset (fun _ : n => sᶜ) := by
    ext f
    simp only [missing, mem_inf, mem_filter, mem_univ, true_and,
      Fintype.mem_piFinset, mem_compl]
    constructor
    · intro h j hj
      exact h (f j) hj j rfl
    · intro h i hi j hji
      exact h j (hji.symm ▸ hi)
  calc
    A.permanent = ∑ f ∈ univ.inf (fun i => (missing i)ᶜ), ∏ j, A (f j) j := by
      rw [hsurj, permanent_eq_sum_surjective]
    _ = ∑ s ∈ (univ : Finset n).powerset,
        (-1 : ℤ) ^ s.card • ∑ f ∈ s.inf missing, ∏ j, A (f j) j :=
      inclusion_exclusion_sum_inf_compl univ missing (fun f => ∏ j, A (f j) j)
    _ = ∑ s ∈ (univ : Finset n).powerset,
        (-1 : R) ^ s.card * ∏ j, ∑ i ∈ sᶜ, A i j := by
      apply sum_congr rfl
      intro s _
      rw [havoid, ← Finset.prod_univ_sum (fun _ : n => sᶜ) (fun j i => A i j)]
      simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    _ = _ := by
      simp only [powerset_univ]
      apply Fintype.sum_equiv (⟨compl, compl, compl_compl, compl_compl⟩ :
        Finset n ≃ Finset n)
      intro s
      simp only [Equiv.coe_fn_mk, card_compl, Nat.sub_sub_self (card_le_univ s)]

/-- Ryser's formula: a sum over subsets of columns, rather than permutations. -/
theorem permanent_eq_sum_powerset {n R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.permanent = ∑ s ∈ (univ : Finset n).powerset,
      (-1 : R) ^ (Fintype.card n - s.card) * ∏ i, ∑ j ∈ s, A i j := by
  simpa using permanent_eq_sum_powerset_cols Aᵀ

end Matrix
