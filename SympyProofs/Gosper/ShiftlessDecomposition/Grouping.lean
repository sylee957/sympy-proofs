module

public import SympyProofs.Gosper.ShiftlessDecomposition.Classes

/-! Correctness of the ordered occurrence arrays and grouped decomposition. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

/-- Array sorting gives the same nonzero shifts as the finite-set specification. -/
theorem Primitives.Valid.sorted_nonzero_shifts {ops : Primitives K} (hops : ops.Valid)
    (S b : Polynomial K) (hS : S.Monic) (hb : b.Monic)
    (hSs : Squarefree S) (hbs : Squarefree b) :
    ((ops.shifts S b).filter (· != 0) |>.mergeSort (· ≤ ·)).toList =
      ((ops.shiftSet S b).erase 0).sort := by
  rw [Array.toList_mergeSort, Array.toList_filter]
  have hn := (hops.nodup_shifts S b hS hb hSs hbs).filter (· != 0)
  have hp : ((ops.shifts S b).toList.filter (· != 0)).Perm
      (((ops.shiftSet S b).erase 0).sort) := by
    apply (List.perm_ext_iff_of_nodup hn (Finset.sort_nodup _ _)).mpr
    intro h
    simp [and_comm]
  exact ((List.mergeSort_perm _ _).trans hp).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) _) (Finset.pairwise_sort _ _)

/-- Specification of the occurrence loop for a base. -/
def makeGroup (ops : Primitives K) (S : Polynomial K) (ν : Polynomial K → ℕ) (b : Polynomial K) : Group K :=
  ⟨b, (⟨0, ν b⟩ :: ((ops.shiftSet S b).erase 0).sort.map (fun h : ℤ => ⟨h, ν (taylor (h : K) b)⟩)).toArray⟩

/-- Specification of the grouping loop, up to the order of the groups. -/
def groupBlocks (ops : Primitives K) (S : Polynomial K) (ν : Polynomial K → ℕ) (bs : Finset (Polynomial K)) :
    List (Group K) := (bases ops S bs).toList.map (makeGroup ops S ν)

/-- Selecting bases while traversing the blocks gives the same groups, up to order. -/
theorem groupBlocks_filter_perm (ops : Primitives K) (S : Polynomial K)
    (ν : Polynomial K → ℕ) (bs : List (Polynomial K)) (hbs : bs.Nodup) :
    ((bs.filter (fun b => decide (∀ h ∈ ops.shifts S b, 0 ≤ h))).map
      (makeGroup ops S ν)).Perm (groupBlocks ops S ν bs.toFinset) := by
  apply List.Perm.map
  apply (List.perm_ext_iff_of_nodup (hbs.filter _)
    (Finset.nodup_toList _)).mpr
  intro b
  simp [bases]

theorem makeGroup_valid [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ)
    (hν : ∀ b ∈ bs, 0 < ν b) {b : Polynomial K} (hbm : b ∈ bases ops S bs) :
    (makeGroup ops S ν b).Valid := by
  obtain ⟨hbm, hmin⟩ := Finset.mem_filter.mp hbm
  refine ⟨hb.monic b hbm, hb.nonconstant b hbm, hb.squarefree b hbm,
    hb.shiftFree b hbm, rfl, ?_, ?_⟩
  · change (Occurrence.mk 0 (ν b) :: _).Pairwise _
    rw [List.pairwise_cons]
    constructor
    · intro o ho
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ho
      have hh' := Finset.mem_erase.mp ((Finset.mem_sort (· ≤ ·)).mp hh)
      exact lt_of_le_of_ne (hmin h hh'.2) (Ne.symm hh'.1)
    · rw [List.pairwise_map]
      exact ((ops.shiftSet S b).erase 0).sortedLT_sort.pairwise
  · intro o ho
    simp only [makeGroup, List.mem_toArray] at ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨le_rfl, hν b hbm⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ho
      have hh' := Finset.mem_erase.mp ((Finset.mem_sort (· ≤ ·)).mp hh)
      exact ⟨hmin h hh'.2, hν _ ((hb.mem_shifts_iff hops hbm h).mp hh'.2)⟩

theorem makeGroup_expand [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ)
    {b : Polynomial K} (hbm : b ∈ bs) :
    (makeGroup ops S ν b).expand =
      ∏ h ∈ ops.shiftSet S b, taylor (h : K) b ^ ν (taylor (h : K) b) := by
  let H := ops.shiftSet S b
  let f := fun h : ℤ => taylor (h : K) b ^ ν (taylor (h : K) b)
  have ht : ((H.erase 0).sort.map f).prod = ∏ h ∈ H.erase 0, f h := by
    rw [← List.prod_toFinset f ((H.erase 0).sort_nodup (· ≤ ·)), Finset.sort_toFinset]
  simp only [makeGroup, Group.expand, ← Array.prod_toList, Array.toList_map,
    List.map_cons, List.prod_cons, List.map_map,
    Function.comp_def, Int.cast_zero, taylor_zero]
  change b ^ ν b * ((H.erase 0).sort.map f).prod = ∏ h ∈ H, f h
  rw [ht]
  simpa [f] using Finset.mul_prod_erase H f (hb.zero_mem_shifts hops hbm)

theorem groupBlocks_valid [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ)
    (hν : ∀ b ∈ bs, 0 < ν b) :
    ∀ g ∈ groupBlocks ops S ν bs, g.Valid := by
  intro g hg
  obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hg
  exact makeGroup_valid hops hb ν hν (Finset.mem_toList.mp hbm)

theorem groupBlocks_separated [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ) :
    (groupBlocks ops S ν bs).Pairwise (fun a b => ShiftCoprime a.base b.base) := by
  unfold groupBlocks
  rw [List.pairwise_map]
  apply (Finset.nodup_toList _).pairwise_of_forall_ne
  intro a ha b hb' hab
  exact hb.bases_separated hops (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb') hab

theorem groupBlocks_reconstruct [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ) :
    ((groupBlocks ops S ν bs).map Group.expand).prod = ∏ b ∈ bs, b ^ ν b := by
  unfold groupBlocks
  rw [List.map_map, Finset.prod_map_toList]
  calc
    _ = ∏ b ∈ bases ops S bs, ∏ h ∈ ops.shiftSet S b, taylor (h : K) b ^ ν (taylor (h : K) b) := by
      apply Finset.prod_congr rfl
      intro b hbm
      exact makeGroup_expand hops hb ν (Finset.mem_filter.mp hbm).1
    _ = _ := hb.prod_classes hops ν

end Gosper.ShiftlessDecomposition
