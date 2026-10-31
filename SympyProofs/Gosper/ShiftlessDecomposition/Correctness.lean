module

public import SympyProofs.Gosper.ShiftlessDecomposition.Grouping
public import SympyProofs.Gosper.ShiftlessDecomposition.Layers
public import SympyProofs.Gosper.ShiftlessDecomposition.Support
public import Std.Tactic.Do
public import Std.WP

/-!
# Soundness and completeness of shiftless decomposition

`decompose` is defined on every input without proof arguments.
Over a characteristic-zero field, under the primitive contracts and the nonzero-input assumption,
`decompose_sound` proves the complete mathematical specification of its result.
`decompose_complete` states successful construction explicitly, while
`exists_valid_iff` identifies nonzero input as the exact existence condition.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial
open scoped Std.WP

/-- The mathematical specifications of the stages imply the output contract. -/
private theorem valid_of_partition [CharZero K] (ops : Primitives K) (hops : ops.Valid)
    (D : Polynomial K) (hD : D ≠ 0) (layers : List (Polynomial K))
    (S : Polynomial K) (blocks : List (Polynomial K)) (groups : Array (Group K))
    (hlprod : layers.prod = C D.leadingCoeff⁻¹ * D)
    (hl : ∀ a ∈ layers, a.Monic ∧ Squarefree a)
    (hS : SupportInvariant layers S)
    (hpart : Partition S (shiftTests ops S layers) blocks)
    (hg : groups.toList.Perm (groupBlocks ops S (exponent layers) blocks.toFinset)) :
    Valid D groups := by
  obtain ⟨hSm, hSs, hlS, hSprod, hSl⟩ := hS
  have hblocks := hpart.blockSystem hops hSm hSs hlS hSl
  let ν := exponent layers
  have hν : ∀ b ∈ blocks.toFinset, 0 < ν b := fun b hb =>
    hpart.exponent_pos hops hSm hSs hlS hSprod (List.mem_toFinset.mp hb)
  have he : ((groupBlocks ops S ν blocks.toFinset).map Group.expand).prod =
      C D.leadingCoeff⁻¹ * D := by
    rw [groupBlocks_reconstruct hops hblocks ν,
      ← hpart.reconstruct_powers hops hSm hSs hlS (fun a ha => (hl a ha).1), hlprod]
  refine ⟨hD, ?_, ?_, ?_⟩
  · rw [← Array.prod_toList, Array.toList_map, (hg.map Group.expand).prod_eq, he,
      ← mul_assoc, ← C_mul]
    simp [leadingCoeff_ne_zero.mpr hD]
  · intro g hgm
    exact groupBlocks_valid hops hblocks ν hν g (hg.mem_iff.mp (Array.mem_toList_iff.mpr hgm))
  · exact (hg.pairwise_iff (fun h => h.symm)).mpr (groupBlocks_separated hops hblocks ν)

theorem decompose_sound [CharZero K] (ops : Primitives K) (hops : ops.Valid)
    (D : Polynomial K) (hD : D ≠ 0) : Valid D (decompose ops D) := by
  let F := C D.leadingCoeff⁻¹ * D
  have hF : F.Monic := by
    simpa [F, mul_comm] using monic_mul_leadingCoeff_inv hD
  have hFdegree : F.natDegree = D.natDegree :=
    natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hD))
  have hFne (hdeg : D.natDegree ≠ 0) : F ≠ 1 := by
    intro heq
    apply hdeg
    rw [← hFdegree, heq, natDegree_one]
  have hlength (hdeg : D.natDegree ≠ 0) :
      F.natDegree - 1 + 1 = F.natDegree := by
    simp [hFdegree]
    omega
  generalize he : decompose ops D = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ (remaining, layers) =>
      LayerInvariant F (pref.length + 1) remaining layers ∧ layers[0]? = some S
  · by
      rename_i hdeg start rem la hi
      exact fun pref _ tests => tests.toList =
        pref.flatMap (fun h : ℤ => la.toList.map (fun a => taylor (h : K) a))
  · by
      rename_i hdeg start rem la hi ta ht
      exact fun pref _ blocks => blocks.toList = refineBlocks ops S pref
  · by
      rename_i hdeg start rem la hi ta ht ba hb
      exact fun pref _ groups => groups.toList =
        (pref.filter (fun b => decide (∀ h ∈ ops.shifts S b, 0 ≤ h))).map
          (makeGroup ops S (exponent la.toList))
  · by
      rename_i hdeg start rem la hi ta ht ba hb pref b suff hs ga hg hbase
      exact fun pref _ multiplicity => multiplicity.down = exponent pref b
  · by
      rename_i hdeg start rem la hi ta ht ba hb pref b suff hs ga hg hbase bm hm
      exact fun pref _ os => os.down.toList = occurrences.down.toList ++
        pref.map (fun h : ℤ => ⟨h, exponent la.toList (taylor (h : K) b)⟩)
  · fun pref _ multiplicity => multiplicity.down = exponent pref shifted
  · by
      rename_i pref test suff hs old hb
      exact fun pref _ next => next.toList = pref.flatMap (fun b => refineBlocks ops b [test])
  · by
      rename_i pref h suff hs old ht
      exact fun pref _ current => current.toList = old.toList ++ pref.map (fun a => taylor (h : K) a)
  case vc1 =>
    rename_i hdeg
    refine ⟨hD, ?_, ?_, ?_⟩
    · simpa [leadingCoeff, hdeg] using
        (eq_C_of_natDegree_eq_zero hdeg).symm
    · simp
    · simp
  case vc2 =>
    rename_i hdeg start
    refine ⟨?_, by simp [layers]⟩
    simpa [F, S, layers, remaining, Primitives.squarefreePart] using
      (LayerInvariant.initial hF).step hops (hFne hdeg)
  case vc3 => simp
  case vc4 =>
    rename_i hdeg start rem la hi ta ht
    have hi' : LayerInvariant F F.natDegree rem la := by
      simpa [← hFdegree, hlength hdeg] using hi.1
    have hS : S ≠ 1 := by
      simpa [hi.2] using hi'.support_ne_one (hFne hdeg)
    simp [refineBlocks, hS]
  case vc5 => simp
  case vc6 =>
    rename_i hdeg start rem la hi ta ht ba hb ga hg
    have hS : SupportInvariant la.toList S := by simpa [hi.2] using hi.1.support
    simp only [Std.Internal.ForIn.toList_array] at ht hb hg
    have hi' : LayerInvariant F F.natDegree rem la := by
      simpa [← hFdegree, hlength hdeg] using hi.1
    obtain ⟨hlprod, hl⟩ := hi'.finish
    change ta.toList = shiftTests ops S la.toList at ht
    have hpart : Partition S (shiftTests ops S la.toList) ba.toList := by
      rw [hb, ht]
      exact refineBlocks_spec ops hops S hS.monic hS.squarefree (shiftTests ops S la.toList)
    apply valid_of_partition ops hops D hD la.toList S ba.toList ga hlprod hl hS hpart
    rw [hg]
    exact groupBlocks_filter_perm ops S (exponent la.toList) ba.toList
      (hpart.nodup hS.squarefree)
  case vc7 => simp [exponent]
  case vc8 => simp_all +zetaDelta
  case vc9 =>
    rename_i hdeg start rem la hi ta ht ba hb emptyGroups pref b suff hs ga hg hbase
      bm hbm occs ho
    have hS : SupportInvariant la.toList S := by simpa [hi.2] using hi.1.support
    simp only [Std.Internal.ForIn.toList_array] at hb hs
    have hmem : b ∈ refineBlocks ops S ta.toList := by
      rw [← hb, hs]
      simp
    have hpart := refineBlocks_spec ops hops S hS.monic hS.squarefree ta.toList
    have hsorted := hops.sorted_nonzero_shifts S b hS.monic (hpart.monic b hmem)
      hS.squarefree (hpart.squarefree b hmem)
    simp only [Std.Internal.ForIn.toList_array] at ho hbm
    have hgroup : Group.mk b occs.down = makeGroup ops S (exponent la.toList) b := by
      unfold makeGroup
      congr 1
      apply Array.toList_inj.mp
      simpa [occurrences, shifts, hbm, hsorted] using ho
    simp only [shifts] at hbase
    simp [groups, Array.toList_push, hg, List.filter_append, List.filter_cons, hgroup]
    rw [ite_eq_left hbase]
    rfl
  case vc10 => simp [exponent]
  case vc11 =>
    simp_all +zetaDelta [Array.toList_push]
  case vc12 | vc13 | vc14 | vc15 =>
    simp_all +zetaDelta [exponent, List.filter_append]
  case vc16 =>
    rename_i pref b suff hs old hg hn
    simp only [shifts] at hn
    simpa [List.filter_append, hn] using hg
  case vc17 => simp
  case vc18 =>
    rename_i pref test suff hs old hb new hn
    simpa [refineBlocks_append, ← hb] using hn
  case vc19 =>
    rename_i old hb empty pref b suff hs acc hn jp hg pushed hq
    simp only [Std.Internal.ForIn.toList_array] at hs
    have hm : b ∈ old.toList := by rw [hs]; simp
    have hb1 : b ≠ 1 := refineBlocks_ne_one ops _ _ (hb ▸ hm)
    simp_all +zetaDelta [Array.toList_push, List.flatMap_append, refineBlocks, List.append_assoc]
  case vc20 | vc21 =>
    rename_i old hb empty pref b suff hs acc hn jp hg hq
    simp only [Std.Internal.ForIn.toList_array] at hs
    have hm : b ∈ old.toList := by rw [hs]; simp
    have hb1 : b ≠ 1 := refineBlocks_ne_one ops _ _ (hb ▸ hm)
    simp_all +zetaDelta [Array.toList_push, List.flatMap_append, refineBlocks]
  case vc22 =>
    rename_i old hb pref b suff hs acc hn jp hg hq
    simp only [Std.Internal.ForIn.toList_array] at hs
    have hm : b ∈ old.toList := by rw [hs]; simp
    have hb1 : b ≠ 1 := refineBlocks_ne_one ops _ _ (hb ▸ hm)
    simp_all +zetaDelta [refineBlocks]
  case vc23 => simp
  case vc24 =>
    rename_i pref h suff hs old ht new hn
    simpa [List.flatMap_append, ht] using hn
  case vc25 =>
    rename_i pref a suff hs old ht
    simp [tests, Array.toList_push, ht, List.append_assoc]
  case vc26 =>
    rename_i pref n suff hs rem layers hi hr
    refine ⟨?_, hi.2⟩
    have hdeg : D.natDegree ≠ 0 := by assumption
    simpa [← hFdegree, hlength hdeg] using hi.1.stop hr
  case vc27 =>
    rename_i pref n suff hs old oldLayers hi hne
    refine ⟨?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton, Primitives.squarefreePart]
        using hi.1.step hops hne
    · have hsize : 0 < oldLayers.size := by
        by_contra hn
        have hz : oldLayers.size = 0 := by omega
        have he : oldLayers = #[] := Array.eq_empty_of_size_eq_zero hz
        simpa [he] using hi.2
      simpa only [layers, Array.getElem?_push_lt hsize, Array.getElem?_eq_getElem hsize] using hi.2

/-- Construction always returns a valid result when its preconditions hold. -/
theorem decompose_complete [CharZero K] (ops : Primitives K) (hops : ops.Valid)
    (D : Polynomial K) (hD : D ≠ 0) :
    ∃ groups, decompose ops D = groups ∧ Valid D groups :=
  ⟨decompose ops D, rfl, decompose_sound ops hops D hD⟩

/-- A nonzero polynomial is exactly the precondition for a shiftless decomposition. -/
theorem exists_valid_iff [CharZero K] (ops : Primitives K) (hops : ops.Valid) (D : Polynomial K) :
    (∃ groups : Array (Group K), Valid D groups) ↔ D ≠ 0 := by
  constructor
  · rintro ⟨d, hd⟩
    exact hd.nonzero
  · intro hD
    exact ⟨decompose ops D, decompose_sound ops hops D hD⟩

theorem decompose_reconstruct [CharZero K] (ops : Primitives K) (hops : ops.Valid)
    (D : Polynomial K) (hD : D ≠ 0) :
    C D.leadingCoeff * ((decompose ops D).map Group.expand).prod = D :=
  (decompose_sound ops hops D hD).reconstruct

/-- Evaluation preserves the exact reconstruction identity. -/
theorem decompose_eval [CharZero K] (ops : Primitives K) (hops : ops.Valid)
    (D : Polynomial K) (hD : D ≠ 0) (x : K) :
    D.eval x = D.leadingCoeff *
      ((decompose ops D).map fun g =>
        (g.occurrences.map fun o =>
          g.base.eval (x + (o.shift : K)) ^ o.multiplicity).prod).prod :=
  (decompose_sound ops hops D hD).eval x

@[simp] theorem decompose_constant (ops : Primitives K) (c : K) :
    decompose ops (C c) = #[] := by
  simp [decompose]

@[simp] theorem decompose_zero (ops : Primitives K) :
    decompose ops 0 = #[] := by
  simpa using decompose_constant ops 0

end Gosper.ShiftlessDecomposition
