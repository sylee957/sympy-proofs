module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator

/-!
# Reachable states

This file is about matrices only. `Reachable Q i j` says that a chain with generator
`Q` in state `i` is in state `j` after some time with positive probability.

No particular time is part of the definition, and none is needed. The chain stays where
it is with positive probability, so a state that can be reached in some time can be
reached in any longer time. This is `IsGenerator.transition_pos_add`. So if one state
can be reached from every state, a single positive time works for all of them, which is
`exists_transition_pos_of_reachable`.

Reachability can be read off the generator without computing any exponential. Say there
is an arrow from `a` to `b` when the rate `Q a b` is positive. Then `j` can be reached
from `i` exactly when a chain of arrows leads from `i` to `j`. This is
`IsGenerator.reachable_iff_reflTransGen`. A chain of no arrows is allowed, so every
state can be reached from itself.

One direction holds because the chain moves along a positive rate with positive
probability, by `transition_pos_of_pos`, and reachability is transitive. For the other
direction, the states at the end of some chain of arrows from `i` form a set that no
rate leads out of. Then no transition leads out of it either, by
`transition_apply_eq_zero_of_forall_eq_zero`. The transitions from such a set also
depend only on the rows of the set, by `transition_apply_eq_of_forall_eq`.

Last, from every state one can reach a state `a` that can be reached back from every
state reachable from `a`. This is `IsGenerator.exists_reachable_forall_reachable`. The
chain can never leave the states reachable from such an `a`, and it moves between all
of them. Every state reachable from such an `a` is of the same kind, by
`IsGenerator.forall_reachable_of_reachable`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- State `j` can be reached from state `i`: after some time the chain started in `i` is
in `j` with positive probability. -/
def Reachable (Q : Matrix ι ι ℝ) (i j : ι) : Prop :=
  ∃ t : ℝ≥0, 0 < transition Q t i j

/-- A state that can be reached in some time can be reached in any longer time. -/
theorem IsGenerator.transition_pos_add (hQ : IsGenerator Q) {s : ℝ≥0} {i j : ι}
    (h : 0 < transition Q s i j) (u : ℝ≥0) :
    0 < transition Q ((s + u : ℝ≥0) : ℝ) i j := by
  rw [NNReal.coe_add, transition_add, Matrix.mul_apply]
  refine Finset.sum_pos' (fun k _ => mul_nonneg
    ((hQ.transition_mem_rowStochastic s s.coe_nonneg).1 i k)
    ((hQ.transition_mem_rowStochastic u u.coe_nonneg).1 k j)) ⟨j, Finset.mem_univ j, ?_⟩
  exact mul_pos h
    (transition_diag_pos_of_offDiag_nonneg Q hQ.offDiag_nonneg u u.coe_nonneg j)

/-- If one state can be reached from every state, it can be reached from every state in
one common positive time. -/
theorem exists_transition_pos_of_reachable (hQ : IsGenerator Q) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) :
    ∃ t₀ : ℝ≥0, 0 < t₀ ∧ ∀ i, 0 < transition Q t₀ i j₀ := by
  choose τ hτ using h
  refine ⟨1 + ∑ i, τ i, add_pos_of_pos_of_nonneg one_pos (zero_le (a := ∑ i, τ i)),
    fun i => ?_⟩
  have hle : τ i ≤ 1 + ∑ i, τ i :=
    (Finset.single_le_sum (fun k _ => zero_le (a := τ k)) (Finset.mem_univ i)).trans
      le_add_self
  have := hQ.transition_pos_add (hτ i) (1 + ∑ i, τ i - τ i)
  rwa [add_tsub_cancel_of_le hle] at this

/-! ### Reading reachability off the generator -/

/-- Every state can be reached from itself. -/
theorem Reachable.refl (Q : Matrix ι ι ℝ) (i : ι) : Reachable Q i i :=
  ⟨0, by simp⟩

/-- A state that can be reached from a reachable state can be reached. -/
theorem IsGenerator.reachable_trans (hQ : IsGenerator Q) {i j k : ι}
    (hij : Reachable Q i j) (hjk : Reachable Q j k) : Reachable Q i k := by
  obtain ⟨s, hs⟩ := hij
  obtain ⟨u, hu⟩ := hjk
  refine ⟨s + u, ?_⟩
  rw [NNReal.coe_add, transition_add, Matrix.mul_apply]
  exact Finset.sum_pos' (fun l _ => mul_nonneg
    ((hQ.transition_mem_rowStochastic s s.coe_nonneg).1 i l)
    ((hQ.transition_mem_rowStochastic u u.coe_nonneg).1 l k))
    ⟨j, Finset.mem_univ j, mul_pos hs hu⟩

/-- A positive rate from `i` to `j` makes `j` reachable from `i`. -/
theorem IsGenerator.reachable_of_pos (hQ : IsGenerator Q) {i j : ι} (h : 0 < Q i j) :
    Reachable Q i j :=
  ⟨1, by simpa using transition_pos_of_pos Q hQ.offDiag_nonneg 1 one_pos h⟩

/-- If no rate leads out of a set of states, then no transition leads out of it. -/
theorem transition_apply_eq_zero_of_forall_eq_zero {S : Set ι}
    (hS : ∀ a b, a ∈ S → b ∉ S → Q a b = 0) (t : ℝ) {a b : ι} (ha : a ∈ S) (hb : b ∉ S) :
    transition Q t a b = 0 := by
  have hpow : ∀ (k : ℕ) (a b : ι), a ∈ S → b ∉ S → ((t • Q) ^ k) a b = 0 := by
    intro k
    induction k with
    | zero =>
      intro a b ha hb
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [hab]
    | succ k ih =>
      intro a b ha hb
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l ∈ S
      · simp [Matrix.smul_apply, hS l b hl hb]
      · simp [ih a l ha hl]
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp (t • Q)) a) b
  refine hs.unique ?_
  simp [hpow _ a b ha hb]

/-- If no rate leads out of a set of states, the transitions from the set depend only on
the rows of the set. -/
theorem transition_apply_eq_of_forall_eq {Q' : Matrix ι ι ℝ} {S : Set ι}
    (hS : ∀ a b, a ∈ S → b ∉ S → Q a b = 0) (hQ' : ∀ a b, a ∈ S → Q' a b = Q a b) (t : ℝ)
    {a : ι} (ha : a ∈ S) (b : ι) : transition Q' t a b = transition Q t a b := by
  have hpow : ∀ (k : ℕ) (a b : ι), a ∈ S → ((t • Q') ^ k) a b = ((t • Q) ^ k) a b := by
    intro k
    induction k with
    | zero =>
      intro a b _
      simp
    | succ k ih =>
      intro a b ha
      rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ∈ S
      · rw [ih l b hl, Matrix.smul_apply, Matrix.smul_apply, hQ' a l ha]
      · simp [Matrix.smul_apply, hQ' a l ha, hS a l ha hl]
  have hs := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp (t • Q)) a) b
  have hs' := Pi.hasSum.mp (Pi.hasSum.mp (MatrixExponential.hasSum_exp (t • Q')) a) b
  refine hs'.unique ?_
  change HasSum _ (MatrixExponential.exp (t • Q) a b)
  simpa [hpow _ a b ha] using hs

/-- A chain of positive rates from `i` to `j` makes `j` reachable from `i`. -/
theorem IsGenerator.reachable_of_reflTransGen (hQ : IsGenerator Q) {i j : ι}
    (h : Relation.ReflTransGen (fun a b => 0 < Q a b) i j) : Reachable Q i j := by
  induction h with
  | refl => exact Reachable.refl Q i
  | tail _ hbc ih => exact hQ.reachable_trans ih (hQ.reachable_of_pos hbc)

/-- A state that can be reached from `i` is at the end of a chain of positive rates that
starts at `i`. -/
theorem IsGenerator.reflTransGen_of_reachable (hQ : IsGenerator Q) {i j : ι}
    (h : Reachable Q i j) : Relation.ReflTransGen (fun a b => 0 < Q a b) i j := by
  obtain ⟨t, ht⟩ := h
  by_contra hj
  have hS : ∀ a b, a ∈ {b | Relation.ReflTransGen (fun a b => 0 < Q a b) i b} →
      b ∉ {b | Relation.ReflTransGen (fun a b => 0 < Q a b) i b} → Q a b = 0 := by
    intro a b ha hb
    by_contra hne
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    exact hb (ha.tail ((hQ.offDiag_nonneg a b hab).lt_of_ne' hne))
  exact ht.ne' (transition_apply_eq_zero_of_forall_eq_zero hS t Relation.ReflTransGen.refl hj)

/-- Reachability can be read off the generator: `j` can be reached from `i` exactly when
a chain of positive rates leads from `i` to `j`. -/
theorem IsGenerator.reachable_iff_reflTransGen (hQ : IsGenerator Q) {i j : ι} :
    Reachable Q i j ↔ Relation.ReflTransGen (fun a b => 0 < Q a b) i j :=
  ⟨hQ.reflTransGen_of_reachable, hQ.reachable_of_reflTransGen⟩

/-! ### States that can be reached back -/

/-- No rate leads from a state that can be reached from `a` to a state that cannot. -/
theorem IsGenerator.eq_zero_of_reachable_of_not_reachable (hQ : IsGenerator Q) {a i j : ι}
    (hi : Reachable Q a i) (hj : ¬Reachable Q a j) : Q i j = 0 := by
  by_contra hne
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  exact hj (hQ.reachable_trans hi
    (hQ.reachable_of_pos ((hQ.offDiag_nonneg i j hij).lt_of_ne' hne)))

/-- From every state one can reach a state `a` that can be reached back from every state
reachable from `a`. -/
theorem IsGenerator.exists_reachable_forall_reachable (hQ : IsGenerator Q) (i : ι) :
    ∃ a, Reachable Q i a ∧ ∀ b, Reachable Q a b → Reachable Q b a := by
  classical
  let R : ι → Finset ι := fun a => Finset.univ.filter (Reachable Q a)
  have hR : ∀ a b, b ∈ R a ↔ Reachable Q a b := fun a b => by simp [R]
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (R i) (fun a => (R a).card)
    ⟨i, (hR i i).2 (Reachable.refl Q i)⟩
  have hia : Reachable Q i a := (hR i a).1 ha
  refine ⟨a, hia, fun b hab => ?_⟩
  have hsub : R b ⊆ R a := fun c hc =>
    (hR a c).2 (hQ.reachable_trans hab ((hR b c).1 hc))
  have heq : R b = R a := Finset.eq_of_subset_of_card_le hsub
    (hmin b ((hR i b).2 (hQ.reachable_trans hia hab)))
  exact (hR b a).1 (heq ▸ (hR a a).2 (Reachable.refl Q a))

/-- A state reachable from a state that can be reached back can be reached back too. -/
theorem IsGenerator.forall_reachable_of_reachable (hQ : IsGenerator Q) {a b : ι}
    (ha : ∀ c, Reachable Q a c → Reachable Q c a) (hab : Reachable Q a b) :
    ∀ c, Reachable Q b c → Reachable Q c b :=
  fun c hbc => hQ.reachable_trans (ha c (hQ.reachable_trans hab hbc)) hab

end SympyProofs.FiniteMarkovChain
