module

public import SympyProofs.Sum.ShiftlessDecomposition.Multiplicities

/-! Partition refined blocks into integer-translation classes. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

structure BlockSystem (S : Polynomial K) (bs : Finset (Polynomial K)) : Prop where
  monic : ∀ b ∈ bs, b.Monic
  nonconstant : ∀ b ∈ bs, 0 < b.natDegree
  squarefree : ∀ b ∈ bs, Squarefree b
  shiftFree : ∀ b ∈ bs, ShiftFree b
  reconstruct : (∏ b ∈ bs, b) = S
  compatible : ∀ b ∈ bs, ∀ c ∈ bs, ∀ h : ℤ,
    ¬IsCoprime c (taylor (h : K) b) → taylor (h : K) b = c

theorem Partition.blockSystem [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic) (hs : Squarefree S)
    (hl : ∀ a ∈ layers, a ∣ S) (hSl : S = 1 ∨ S ∈ layers)
    (hb : Partition S (shiftTests ops S layers) bs) :
    BlockSystem S bs.toFinset where
  monic b hm := hb.monic b (List.mem_toFinset.mp hm)
  nonconstant b hm := hb.nonconstant b (List.mem_toFinset.mp hm)
  squarefree b hm := hb.squarefree b (List.mem_toFinset.mp hm)
  shiftFree _b hm := hb.shiftFree hops hS hs hl hSl (List.mem_toFinset.mp hm)
  reconstruct := hb.prod_toFinset hs
  compatible _b hm _c hn h hc :=
    hb.shift_overlap_eq hops hS hs hl hSl (List.mem_toFinset.mp hm) (List.mem_toFinset.mp hn) h hc

omit [DecidableEq K] in
theorem BlockSystem.monic_support {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) :
    S.Monic := hb.reconstruct ▸ monic_prod_of_monic bs id hb.monic

omit [DecidableEq K] in
theorem BlockSystem.squarefree_support {S : Polynomial K} {bs : Finset (Polynomial K)}
    (hb : BlockSystem S bs) : Squarefree S := by
  rw [← hb.reconstruct]
  apply Finset.squarefree_prod_of_pairwise_isCoprime (f := id) ?_ hb.squarefree
  intro b hbm c hcm hbc
  apply IsCoprime.isRelPrime
  by_contra hc
  have hnc : ¬IsCoprime c (taylor ((0 : ℤ) : K) b) := by
    simpa using (fun hcb : IsCoprime c b => hc hcb.symm)
  exact hbc (by simpa using hb.compatible b hbm c hcm 0 hnc)

omit [DecidableEq K] in
theorem BlockSystem.divides {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs)
    {b : Polynomial K} (hbm : b ∈ bs) : b ∣ S := by
  rw [← hb.reconstruct]
  exact Finset.dvd_prod_of_mem id hbm

theorem BlockSystem.mem_shifts_iff [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) {b : Polynomial K} (hbm : b ∈ bs)
    (h : ℤ) : h ∈ ops.shiftSet S b ↔ taylor (h : K) b ∈ bs := by
  rw [hops.mem_shiftSet S b hb.monic_support (hb.monic b hbm)
    hb.squarefree_support (hb.squarefree b hbm) h]
  constructor
  · intro hn
    by_contra hm
    apply hn
    rw [← hb.reconstruct]
    apply IsCoprime.prod_left
    intro c hc
    by_contra hnc
    exact hm ((hb.compatible b hbm c hc h hnc).symm ▸ hc)
  · intro hm hc
    exact not_isUnit_of_natDegree_pos (taylor (h : K) b) (hb.nonconstant _ hm)
      (hc.symm.isUnit_of_dvd (hb.divides hm))

theorem BlockSystem.zero_mem_shifts [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) {b : Polynomial K} (hbm : b ∈ bs) :
    0 ∈ ops.shiftSet S b := (hb.mem_shifts_iff hops hbm 0).mpr (by simpa using hbm)

/-- The representatives selected by the base test in the grouping loop. -/
def bases (ops : Primitives K) (S : Polynomial K) (bs : Finset (Polynomial K)) : Finset (Polynomial K) :=
  bs.filter (fun b => ∀ h ∈ ops.shiftSet S b, 0 ≤ h)

theorem BlockSystem.exists_base [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) {b : Polynomial K} (hbm : b ∈ bs) :
    ∃ a ∈ bases ops S bs, ∃ h ∈ ops.shiftSet S a, taylor (h : K) a = b := by
  let H := ops.shiftSet S b
  have hH : H.Nonempty := ⟨0, hb.zero_mem_shifts hops hbm⟩
  let k := H.min' hH
  have hk : k ∈ H := H.min'_mem hH
  let a := taylor (k : K) b
  have ham : a ∈ bs := (hb.mem_shifts_iff hops hbm k).mp hk
  have ha : a ∈ bases ops S bs := by
    apply Finset.mem_filter.mpr
    refine ⟨ham, ?_⟩
    intro h hh
    have hkh : k + h ∈ H := by
      apply (hb.mem_shifts_iff hops hbm (k + h)).mpr
      simpa [a, taylor_taylor, add_comm] using (hb.mem_shifts_iff hops ham h).mp hh
    have := H.min'_le _ hkh
    change k ≤ k + h at this
    omega
  refine ⟨a, ha, -k, ?_, ?_⟩
  · apply (hb.mem_shifts_iff hops ham (-k)).mpr
    simpa [a, taylor_taylor, add_comm] using hbm
  · simp [a, taylor_taylor, add_comm]

theorem BlockSystem.base_unique [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs)
    {a b : Polynomial K} (ha : a ∈ bases ops S bs) (hb' : b ∈ bases ops S bs)
    {h k : ℤ} (he : taylor (h : K) a = taylor (k : K) b) : a = b ∧ h = k := by
  obtain ⟨ham, ha0⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbm, hb0⟩ := Finset.mem_filter.mp hb'
  have hab : taylor ((h - k : ℤ) : K) a = b := by
    have ht := congrArg (fun p => taylor ((-k : ℤ) : K) p) he
    simpa [taylor_taylor, sub_eq_add_neg, add_comm] using ht
  have hba : taylor ((k - h : ℤ) : K) b = a := by
    have ht := congrArg (fun p => taylor ((-h : ℤ) : K) p) he.symm
    simpa [taylor_taylor, sub_eq_add_neg, add_comm] using ht
  have hh := ha0 (h - k) ((hb.mem_shifts_iff hops ham _).mpr (hab.symm ▸ hbm))
  have hk := hb0 (k - h) ((hb.mem_shifts_iff hops hbm _).mpr (hba.symm ▸ ham))
  have heq : h = k := by omega
  refine ⟨?_, heq⟩
  simpa [heq] using hab

theorem BlockSystem.bases_separated [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs)
    {a b : Polynomial K} (ha : a ∈ bases ops S bs) (hb' : b ∈ bases ops S bs) (hab : a ≠ b) :
    ShiftCoprime a b := by
  intro h
  by_contra hc
  have he := hb.compatible b (Finset.mem_filter.mp hb').1 a (Finset.mem_filter.mp ha).1 h hc
  have hu := hb.base_unique hops hb' ha (h := h) (k := 0) (by simpa using he)
  exact hab hu.1.symm

theorem BlockSystem.prod_classes [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {bs : Finset (Polynomial K)} (hb : BlockSystem S bs) (ν : Polynomial K → ℕ) :
    (∏ a ∈ bases ops S bs, ∏ h ∈ ops.shiftSet S a, taylor (h : K) a ^ ν (taylor (h : K) a)) =
      ∏ b ∈ bs, b ^ ν b := by
  rw [Finset.prod_sigma']
  apply Finset.prod_bij (fun u _ => taylor (u.2 : K) u.1)
  · intro u hu
    obtain ⟨ha, hh⟩ := Finset.mem_sigma.mp hu
    exact (hb.mem_shifts_iff hops (Finset.mem_filter.mp ha).1 u.2).mp hh
  · intro u hu v hv he
    obtain ⟨ha, _⟩ := Finset.mem_sigma.mp hu
    obtain ⟨hb', _⟩ := Finset.mem_sigma.mp hv
    obtain ⟨hab, hhk⟩ := hb.base_unique hops ha hb' he
    cases u
    cases v
    simp_all
  · intro b hbm
    obtain ⟨a, ha, h, hh, he⟩ := hb.exists_base hops hbm
    exact ⟨⟨a, h⟩, Finset.mem_sigma.mpr ⟨ha, hh⟩, he⟩
  · intro u hu
    rfl

end Gosper.ShiftlessDecomposition
