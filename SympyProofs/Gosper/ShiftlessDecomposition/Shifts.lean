module

public import SympyProofs.Gosper.ShiftlessDecomposition.Basic
public import SympyProofs.Gosper.ShiftlessDecomposition.Refinement
public import SympyProofs.Gosper.Backend.Resultant

/-! Correctness of shift enumeration and translation of the homogeneous gcd blocks. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K]

open Polynomial

theorem shift_monic {p : Polynomial K} (hp : p.Monic) (h : ℤ) : (taylor (h : K) p).Monic := by
  simpa [Monic] using hp

theorem shift_dvd {p q : Polynomial K} (hpq : p ∣ q) (h : ℤ) : taylor (h : K) p ∣ taylor (h : K) q :=
  (taylorAlgHom (h : K)).toRingHom.map_dvd hpq

theorem shift_coprime {p q : Polynomial K} (hpq : IsCoprime p q) (h : ℤ) :
    IsCoprime (taylor (h : K) p) (taylor (h : K) q) := hpq.map (taylorAlgHom (h : K)).toRingHom

theorem coprime_list_prod_iff (p : Polynomial K) (ps : List (Polynomial K)) :
    IsCoprime p ps.prod ↔ ∀ q ∈ ps, IsCoprime p q := by
  induction ps with
  | nil => simp [isCoprime_one_right]
  | cons q qs ih => simp [IsCoprime.mul_right_iff, ih]

theorem coprime_shift_iff (p q : Polynomial K) (h : ℤ) :
    IsCoprime p (taylor (h : K) q) ↔ IsCoprime (taylor ((-h : ℤ) : K) p) q := by
  constructor
  · intro hc
    simpa [taylor_taylor, add_comm] using shift_coprime hc (-h)
  · intro hc
    simpa [taylor_taylor, add_comm] using shift_coprime hc h

theorem ShiftCoprime.symm {p q : Polynomial K} (h : ShiftCoprime p q) : ShiftCoprime q p := by
  intro z
  simpa [taylor_taylor, add_comm] using (shift_coprime (h (-z)) z).symm

theorem Homogeneous.shift {p a : Polynomial K} (ha : Homogeneous p a) (h : ℤ) :
    Homogeneous (taylor (h : K) p) (taylor (h : K) a) :=
  ha.elim (fun hd => Or.inl (shift_dvd hd h)) (fun hc => Or.inr (shift_coprime hc h))

variable [DecidableEq K]

/-- Finite-set view used in the mathematical specifications. -/
def Primitives.shiftSet (ops : Primitives K) (p q : Polynomial K) : Finset ℤ :=
  (shifts ops p q).toList.toFinset

omit [DecidableEq K] in
@[simp] theorem Primitives.mem_shiftSet (ops : Primitives K) (p q : Polynomial K) (z : ℤ) :
    z ∈ ops.shiftSet p q ↔ z ∈ shifts ops p q := by
  simp [Primitives.shiftSet]

theorem Primitives.Valid.shifts_eq {ops : Primitives K} (h : ops.Valid)
    (p q : Polynomial K) :
    shifts ops p q = ops.integerRoots
      (ops.squarefreePart (Gosper.Algorithm.sylvesterShiftResultant p q)) := by
  simp [shifts, Primitives.squarefreePart, h.resultant_eq,
    Gosper.Algorithm.sylvesterShiftResultant,
    natDegree_map_eq_of_injective Polynomial.C_injective]

theorem Primitives.Valid.mem_shifts [CharZero K] {ops : Primitives K} (h : ops.Valid)
    (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (z : ℤ) :
    z ∈ shifts ops p q ↔ ¬IsCoprime p (taylor (z : K) q) := by
  have hr := Gosper.Algorithm.sylvesterShiftResultant_ne_zero p q hp hq
  rw [h.shifts_eq, h.mem_integerRoots _ (h.squarefreeStep_reconstruct _ hr).1,
    h.squarefreePart_eval_eq_zero hr,
    Gosper.Algorithm.sylvesterShiftResultant_eval]
  simpa [hp] using
    (Polynomial.resultant_eq_zero_iff (f := p) (g := taylor (z : K) q))

theorem Primitives.Valid.mem_shiftSet [CharZero K] {ops : Primitives K} (h : ops.Valid)
    (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (z : ℤ) :
    z ∈ ops.shiftSet p q ↔ ¬IsCoprime p (taylor (z : K) q) := by
  rw [Primitives.mem_shiftSet, h.mem_shifts p q hp hq z]

theorem Primitives.Valid.nodup_shifts {ops : Primitives K} (h : ops.Valid)
    (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
    (shifts ops p q).toList.Nodup := by
  rw [h.shifts_eq]
  exact h.nodup_integerRoots _ (h.squarefreeStep_reconstruct _
    (Gosper.Algorithm.sylvesterShiftResultant_ne_zero p q hp hq)).1

theorem Primitives.Valid.shift_eq_self_iff [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : 0 < p.natDegree) (h : ℤ) : taylor (h : K) p = p ↔ h = 0 := by
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  refine ⟨?_, by rintro rfl; simp⟩
  intro he
  by_contra hh
  have hn : ∀ n : ℕ, taylor (((n : ℤ) * h : ℤ) : K) p = p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Int.cast_add, ← taylor_taylor, he, ih]
  have hnc : ¬IsCoprime p p := fun hc =>
    not_isUnit_of_natDegree_pos p hp (isCoprime_self.mp hc)
  let f : ℕ → {z // z ∈ ops.shiftSet p p} := fun n =>
    ⟨(n : ℤ) * h, (hops.mem_shiftSet p p hp0 hp0 _).mpr (by rw [hn n]; exact hnc)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have heq : (a : ℤ) * h = (b : ℤ) * h := congrArg Subtype.val hab
    exact_mod_cast mul_right_cancel₀ hh heq
  exact Infinite.not_finite (Finite.of_injective f hf)

theorem Primitives.Valid.shift_injective [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : 0 < p.natDegree) : Function.Injective (fun h : ℤ => taylor (h : K) p) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (hops.shift_eq_self_iff hp (a - b)).mp
  have he := congrArg (fun q => taylor ((-b : ℤ) : K) q) hab
  simpa [taylor_taylor, sub_eq_add_neg, add_comm] using he

/-- Pure specification of the polynomials collected by the shift-test loops. -/
def shiftTests (ops : Primitives K) (S : Polynomial K) (layers : List (Polynomial K)) : List (Polynomial K) :=
  (shifts ops S S).toList.flatMap fun h : ℤ => layers.map (fun a => taylor (h : K) a)

omit [DecidableEq K] in
theorem mem_shiftTests (ops : Primitives K) (S a : Polynomial K) (layers : List (Polynomial K)) (h : ℤ) :
    taylor (h : K) a ∈ shiftTests ops S layers ↔
      ∃ z ∈ ops.shiftSet S S, ∃ b ∈ layers, taylor (z : K) b = taylor (h : K) a := by
  simp only [shiftTests, List.mem_flatMap, Array.mem_toList_iff, Primitives.mem_shiftSet, List.mem_map]

theorem Partition.homogeneous_shift [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic)
    (hl : ∀ a ∈ layers, a ∣ S) (hb : Partition S (shiftTests ops S layers) bs)
    {b : Polynomial K} (hmem : b ∈ bs) (a : Polynomial K) (ha : a ∈ layers) (h : ℤ) :
    Homogeneous b (taylor (h : K) a) := by
  by_cases hh : h ∈ ops.shiftSet S S
  · apply hb.homogeneous b hmem
    exact (mem_shiftTests ops S a layers h).mpr ⟨h, hh, a, ha, rfl⟩
  · apply Or.inr
    have hc : IsCoprime S (taylor (h : K) S) := by
      by_contra hnc
      exact hh ((hops.mem_shiftSet S S hS.ne_zero hS.ne_zero h).mpr hnc)
    exact hc.mono (hb.divides b hmem) (shift_dvd (hl a ha) h)

theorem Partition.shift_overlap_dvd [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic)
    (hl : ∀ a ∈ layers, a ∣ S) (hSl : S = 1 ∨ S ∈ layers)
    (hb : Partition S (shiftTests ops S layers) bs)
    {b c : Polynomial K} (hbm : b ∈ bs) (hcm : c ∈ bs) (h : ℤ)
    (hov : ¬IsCoprime c (taylor (h : K) b)) : taylor (h : K) b ∣ c := by
  have hnc : ¬IsCoprime b (taylor ((-h : ℤ) : K) S) := by
    intro hc
    have hc' : IsCoprime S (taylor (h : K) b) := by
      have ht := (coprime_shift_iff b S (-h)).mp hc
      simpa using ht.symm
    exact hov (hc'.of_isCoprime_of_dvd_left (hb.divides c hcm))
  have hSmem : S ∈ layers := hSl.resolve_left (by
    intro he
    apply hnc
    simp [he, isCoprime_one_right])
  have hd : b ∣ taylor ((-h : ℤ) : K) S :=
    (hb.homogeneous_shift hops hS hl hbm S hSmem (-h)).resolve_right hnc
  have hds : taylor (h : K) b ∣ S := by simpa [taylor_taylor, add_comm] using shift_dvd hd h
  apply hb.maximal (taylor (h : K) b) hds ?_ c hcm (fun hc => hov hc.symm)
  intro a ha
  obtain ⟨z, hz, ht⟩ := (List.mem_flatMap.mp ha)
  obtain ⟨t, htm, rfl⟩ := List.mem_map.mp ht
  have hu := hb.homogeneous_shift hops hS hl hbm t htm (z - h)
  simpa [taylor_taylor, add_comm] using hu.shift h

theorem Partition.shift_overlap_eq [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic)
    (hl : ∀ a ∈ layers, a ∣ S) (hSl : S = 1 ∨ S ∈ layers)
    (hb : Partition S (shiftTests ops S layers) bs)
    {b c : Polynomial K} (hbm : b ∈ bs) (hcm : c ∈ bs) (h : ℤ)
    (hov : ¬IsCoprime c (taylor (h : K) b)) : taylor (h : K) b = c := by
  have hbc := hb.shift_overlap_dvd hops hS hl hSl hbm hcm h hov
  have hcb : taylor ((-h : ℤ) : K) c ∣ b := by
    apply hb.shift_overlap_dvd hops hS hl hSl hcm hbm (-h)
    intro hc
    have ht := (coprime_shift_iff b c (-h)).mp hc
    exact hov (by simpa using ht.symm)
  have hcb' : c ∣ taylor (h : K) b := by simpa [taylor_taylor, add_comm] using shift_dvd hcb h
  exact dvd_antisymm_of_normalize_eq (shift_monic (hb.monic b hbm) h).normalize_eq_self
    (hb.monic c hcm).normalize_eq_self hbc hcb'

theorem Partition.shiftFree [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {S : Polynomial K} {layers bs : List (Polynomial K)} (hS : S.Monic)
    (hl : ∀ a ∈ layers, a ∣ S) (hSl : S = 1 ∨ S ∈ layers)
    (hb : Partition S (shiftTests ops S layers) bs)
    {b : Polynomial K} (hbm : b ∈ bs) : ShiftFree b := by
  intro h hh
  by_contra hc
  have he := hb.shift_overlap_eq hops hS hl hSl hbm hbm h hc
  exact hh ((hops.shift_eq_self_iff (hb.nonconstant b hbm) h).mp he)

end Gosper.ShiftlessDecomposition
