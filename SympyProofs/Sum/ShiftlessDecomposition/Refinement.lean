module

public import SympyProofs.Sum.ShiftlessDecomposition.Algorithm
public import SympyProofs.Sum.ShiftlessDecomposition.Progress

/-!
Gcd refinement as successive binary partitions. Each split preserves the product
and separates the factors present in a test polynomial from those absent from it.
The maximality invariant characterizes the coarsest resulting partition.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

def Homogeneous (p a : Polynomial K) : Prop := p ∣ a ∨ IsCoprime p a

structure Partition (p : Polynomial K) (tests blocks : List (Polynomial K)) : Prop where
  monic : ∀ b ∈ blocks, b.Monic
  nonconstant : ∀ b ∈ blocks, 0 < b.natDegree
  squarefree : ∀ b ∈ blocks, Squarefree b
  divides : ∀ b ∈ blocks, b ∣ p
  reconstruct : blocks.prod = p
  homogeneous : ∀ b ∈ blocks, ∀ a ∈ tests, Homogeneous b a
  maximal : ∀ c, c ∣ p → (∀ a ∈ tests, Homogeneous c a) →
    ∀ b ∈ blocks, ¬IsCoprime c b → c ∣ b

/-- Pure specification of the successive gcd partitions in the refinement loop. -/
def refineBlocks (ops : Primitives K) (p : Polynomial K) (tests : List (Polynomial K)) : List (Polynomial K) :=
  if p = 1 then [] else
  match tests with
  | [] => [p]
  | a :: as =>
    let g := ops.gcd p a
    refineBlocks ops g as ++ refineBlocks ops (p / g) as
termination_by tests.length

@[simp] theorem refineBlocks_one (ops : Primitives K) (tests : List (Polynomial K)) :
    refineBlocks ops 1 tests = [] := by
  cases tests <;> simp [refineBlocks]

/-- Processing more tests refines each block already obtained. -/
theorem refineBlocks_append (ops : Primitives K) (p : Polynomial K)
    (tests more : List (Polynomial K)) :
    refineBlocks ops p (tests ++ more) =
      (refineBlocks ops p tests).flatMap (fun b => refineBlocks ops b more) := by
  induction tests generalizing p with
  | nil =>
    by_cases hp : p = 1 <;> simp [refineBlocks, hp]
  | cons a tests ih =>
    by_cases hp : p = 1
    · simp [hp]
    · simp only [List.cons_append, refineBlocks, ite_eq_right hp]
      rw [ih, ih, List.flatMap_append]

theorem refineBlocks_ne_one (ops : Primitives K) (p : Polynomial K)
    (tests : List (Polynomial K)) {b : Polynomial K}
    (hb : b ∈ refineBlocks ops p tests) : b ≠ 1 := by
  induction tests generalizing p with
  | nil =>
    by_cases hp : p = 1
    · simp [hp] at hb
    · simp only [refineBlocks, ite_eq_right hp, List.mem_singleton] at hb
      exact hb ▸ hp
  | cons a tests ih =>
    by_cases hp : p = 1
    · simp [hp] at hb
    · simp only [refineBlocks, ite_eq_right hp, List.mem_append] at hb
      exact hb.elim (ih _) (ih _)

theorem Primitives.Valid.split_spec {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p.Monic) (hs : Squarefree p) (a : Polynomial K) :
    let g := ops.gcd p a
    let q := p / g
    g.Monic ∧ q.Monic ∧ Squarefree g ∧ Squarefree q ∧
      g * q = p ∧ g ∣ a ∧ IsCoprime q a := by
  dsimp only
  let g := ops.gcd p a
  let q := p / g
  let r := a / g
  have hg : g.Monic := hops.gcd_monic p a hp.ne_zero
  have he := hops.refinement_reconstruct p a hp.ne_zero
  change g * q = p ∧ g * r = a at he
  have hs' : Squarefree (g * q) := he.1.symm ▸ hs
  have hqg : IsCoprime q g := (IsRelPrime.of_squarefree_mul hs').isCoprime.symm
  have hqr : IsCoprime q r := by
    dsimp only [q, r]
    dsimp only [g]
    rw [hops.gcd_eq]
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (by simpa [g, hops.gcd_eq] using hg.ne_zero)
  change g.Monic ∧ q.Monic ∧ Squarefree g ∧ Squarefree q ∧
    g * q = p ∧ g ∣ a ∧ IsCoprime q a
  refine ⟨hg, hg.of_mul_monic_left (he.1.symm ▸ hp), hs'.of_mul_left,
    hs'.of_mul_right, he.1, ?_, ?_⟩
  · rw [← he.2]; exact dvd_mul_right _ _
  · rw [← he.2]; exact hqg.mul_right hqr

omit [DecidableEq K] in
private theorem partition_one (tests : List (Polynomial K)) : Partition 1 tests [] := by
  constructor <;> simp

theorem refineBlocks_spec (ops : Primitives K) (hops : ops.Valid)
    (p : Polynomial K) (hp : p.Monic) (hs : Squarefree p) (tests : List (Polynomial K)) :
    Partition p tests (refineBlocks ops p tests) := by
  induction tests generalizing p with
  | nil =>
    by_cases hp1 : p = 1
    · subst p
      simpa [refineBlocks] using partition_one []
    · rw [refineBlocks, ite_eq_right hp1]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using hp
      · simpa using hp.natDegree_pos.mpr hp1
      · simpa using hs
      · simp
      · simp
      · simp
      · intro c hc _ b hb _
        simpa using (List.mem_singleton.mp hb ▸ hc)
  | cons a tests ih =>
    by_cases hp1 : p = 1
    · subst p
      simpa [refineBlocks] using partition_one (a :: tests)
    rw [refineBlocks, ite_eq_right hp1]
    let g := ops.gcd p a
    let q := p / g
    obtain ⟨hgm, hqm, hgs, hqs, he, hga, hqa⟩ := hops.split_spec hp hs a
    have hl := ih g hgm hgs
    have hr := ih q hqm hqs
    have hgp : g ∣ p := by rw [← he]; exact dvd_mul_right _ _
    have hqp : q ∣ p := by rw [← he]; exact dvd_mul_left _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      exact (List.mem_append.mp hb).elim (hl.monic b) (hr.monic b)
    · intro b hb
      exact (List.mem_append.mp hb).elim (hl.nonconstant b) (hr.nonconstant b)
    · intro b hb
      exact (List.mem_append.mp hb).elim (hl.squarefree b) (hr.squarefree b)
    · intro b hb
      exact (List.mem_append.mp hb).elim
        (fun hb => (hl.divides b hb).trans hgp) (fun hb => (hr.divides b hb).trans hqp)
    · rw [List.prod_append, hl.reconstruct, hr.reconstruct]
      exact he
    · intro b hb t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rcases List.mem_append.mp hb with hb | hb
        · exact Or.inl ((hl.divides b hb).trans hga)
        · exact Or.inr (hqa.of_isCoprime_of_dvd_left (hr.divides b hb))
      · exact (List.mem_append.mp hb).elim
          (fun hb => hl.homogeneous b hb t ht) (fun hb => hr.homogeneous b hb t ht)
    · intro c hc hu b hb hcb
      have htail : ∀ t ∈ tests, Homogeneous c t :=
        fun t ht => hu t (List.mem_cons_of_mem a ht)
      rcases List.mem_append.mp hb with hb | hb
      · rcases hu a (List.mem_cons_self ..) with hca | hca
        · apply hl.maximal c ?_ htail b hb hcb
          dsimp only [g]
          rw [hops.gcd_eq]
          exact dvd_gcd hc hca
        · exact (hcb (hca.of_isCoprime_of_dvd_right ((hl.divides b hb).trans hga))).elim
      · rcases hu a (List.mem_cons_self ..) with hca | hca
        · exact (hcb (hqa.symm.mono hca (hr.divides b hb))).elim
        · apply hr.maximal c ?_ htail b hb hcb
          have hcg := hca.of_isCoprime_of_dvd_right hga
          apply hcg.dvd_of_dvd_mul_left
          rwa [he]

omit [DecidableEq K] in
theorem pairwise_coprime_of_squarefree_prod (bs : List (Polynomial K)) (hs : Squarefree bs.prod) :
    bs.Pairwise IsCoprime := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    change Squarefree (b * bs.prod) at hs
    rw [List.pairwise_cons]
    refine ⟨?_, ih hs.of_mul_right⟩
    intro c hc
    exact (IsRelPrime.of_squarefree_mul hs).isCoprime.of_isCoprime_of_dvd_right (List.dvd_prod hc)

omit [DecidableEq K] in
theorem Partition.pairwise {p : Polynomial K} {tests bs : List (Polynomial K)} (h : Partition p tests bs)
    (hs : Squarefree p) : bs.Pairwise IsCoprime :=
  pairwise_coprime_of_squarefree_prod bs (h.reconstruct.symm ▸ hs)

omit [DecidableEq K] in
theorem Partition.nodup {p : Polynomial K} {tests bs : List (Polynomial K)} (h : Partition p tests bs)
    (hs : Squarefree p) : bs.Nodup := by
  change bs.Pairwise (· ≠ ·)
  apply (h.pairwise hs).imp_of_mem
  intro a b ha hb hab he
  subst b
  exact (not_isUnit_of_natDegree_pos a (h.nonconstant a ha)) (isCoprime_self.mp hab)

end Gosper.ShiftlessDecomposition
