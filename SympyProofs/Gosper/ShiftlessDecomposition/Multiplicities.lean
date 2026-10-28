module

public import SympyProofs.Gosper.ShiftlessDecomposition.Shifts

/-! Reconstruct the input from the uniform multiplicities of the refined blocks. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

local instance : DecidableRel (Dvd.dvd : Polynomial K → Polynomial K → Prop) :=
  fun p q => decidable_of_iff (q % p = 0) EuclideanDomain.mod_eq_zero

/-- Specification of the multiplicity loop: count the layers divisible by a block. -/
def exponent (layers : List (Polynomial K)) (b : Polynomial K) : ℕ :=
  (layers.filter (fun a => decide (a % b = 0))).length

theorem exponent_eq (layers : List (Polynomial K)) (b : Polynomial K) :
    exponent layers b = (layers.filter (fun a => decide (b ∣ a))).length := by
  simp [exponent, EuclideanDomain.mod_eq_zero]

theorem Partition.prod_toFinset {S : Polynomial K} {tests bs : List (Polynomial K)}
    (hb : Partition S tests bs) (hs : Squarefree S) : (∏ b ∈ bs.toFinset, b) = S := by
  rw [List.prod_toFinset _ (hb.nodup hs)]
  simpa using hb.reconstruct

theorem Partition.layer_factorization [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic) (hs : Squarefree S)
    (hl : ∀ a ∈ layers, a ∣ S) (hb : Partition S (shiftTests ops S layers) bs)
    {a : Polynomial K} (ha : a ∈ layers) (ham : a.Monic) :
    a = ∏ b ∈ bs.toFinset, if b ∣ a then b else 1 := by
  classical
  let yes := bs.toFinset.filter (fun b => b ∣ a)
  let no := bs.toFinset.filter (fun b => ¬b ∣ a)
  have hp : (∏ b ∈ yes, b) * (∏ b ∈ no, b) = S := by
    rw [Finset.prod_filter_mul_prod_filter_not, hb.prod_toFinset hs]
  have hy : (∏ b ∈ yes, b) ∣ a := by
    apply Finset.prod_dvd_of_coprime
    · intro b hb' c hc' hbc
      exact (hb.pairwise hs).forall
        (List.mem_toFinset.mp (Finset.mem_filter.mp hb').1)
        (List.mem_toFinset.mp (Finset.mem_filter.mp hc').1) hbc
    · intro b hby
      exact (Finset.mem_filter.mp hby).2
  have hcop : IsCoprime a (∏ b ∈ no, b) := by
    apply IsCoprime.prod_right
    intro b hbn
    obtain ⟨hbm, hba⟩ := Finset.mem_filter.mp hbn
    have hu := hb.homogeneous_shift hops hS hl (List.mem_toFinset.mp hbm) a ha 0
    simpa only [shift_zero] using (hu.resolve_left (by simpa using hba)).symm
  have hay : a ∣ ∏ b ∈ yes, b :=
    hcop.dvd_of_dvd_mul_right (hp.symm ▸ hl a ha)
  have hym : (∏ b ∈ yes, b).Monic := monic_prod_of_monic _ _ fun b hby =>
    hb.monic b (List.mem_toFinset.mp (Finset.mem_filter.mp hby).1)
  have he := dvd_antisymm_of_normalize_eq ham.normalize_eq_self hym.normalize_eq_self hay hy
  simpa [yes, Finset.prod_filter] using he

private theorem prod_layers_comm (layers : List (Polynomial K)) (bs : Finset (Polynomial K)) :
    (layers.map (fun a => ∏ b ∈ bs, if b ∣ a then b else 1)).prod =
      ∏ b ∈ bs, (layers.map (fun a => if b ∣ a then b else 1)).prod := by
  induction layers with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.prod_cons, ih, Finset.prod_mul_distrib]

private theorem prod_presence (layers : List (Polynomial K)) (b : Polynomial K) :
    (layers.map (fun a => if b ∣ a then b else 1)).prod =
      b ^ (layers.filter (fun a => decide (b ∣ a))).length := by
  induction layers with
  | nil => simp
  | cons a as ih =>
    by_cases hba : b ∣ a
    · simp [hba, ih, pow_succ, mul_comm]
    · simp [hba, ih]

theorem Partition.reconstruct_powers [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic) (hs : Squarefree S)
    (hl : ∀ a ∈ layers, a ∣ S) (hm : ∀ a ∈ layers, a.Monic)
    (hb : Partition S (shiftTests ops S layers) bs) :
    layers.prod = ∏ b ∈ bs.toFinset, b ^ exponent layers b := by
  calc
    layers.prod = (layers.map (fun a => ∏ b ∈ bs.toFinset, if b ∣ a then b else 1)).prod := by
      conv_lhs => rw [← List.map_id layers]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hb.layer_factorization hops hS hs hl ha (hm a ha)
    _ = ∏ b ∈ bs.toFinset, (layers.map (fun a => if b ∣ a then b else 1)).prod :=
      prod_layers_comm layers bs.toFinset
    _ = ∏ b ∈ bs.toFinset, b ^ exponent layers b := by
      apply Finset.prod_congr rfl
      intro b hbm
      rw [exponent_eq layers b, prod_presence]

theorem Partition.exponent_pos [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic)
    (hl : ∀ a ∈ layers, a ∣ S) (hsp : S ∣ layers.prod)
    (hb : Partition S (shiftTests ops S layers) bs) {b : Polynomial K} (hbm : b ∈ bs) :
    0 < exponent layers b := by
  rw [exponent_eq layers b, List.length_filter_pos_iff]
  by_contra hn
  have hcop : IsCoprime b layers.prod := by
    apply (coprime_list_prod_iff b layers).mpr
    intro a ha
    have hu := hb.homogeneous_shift hops hS hl hbm a ha 0
    apply (by simpa only [shift_zero] using hu : Homogeneous b a).resolve_left
    intro hd
    exact hn ⟨a, ha, by simpa using hd⟩
  exact not_isUnit_of_natDegree_pos b (hb.nonconstant b hbm)
    (hcop.isUnit_of_dvd ((hb.divides b hbm).trans hsp))

end Gosper.ShiftlessDecomposition
