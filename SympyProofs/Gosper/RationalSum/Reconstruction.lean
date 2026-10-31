module

public import SympyProofs.Gosper.RationalSum.Reduction
public import SympyProofs.Gosper.RationalSum.PartialFractions

/-! Connecting a valid shiftless decomposition to partial-fraction reconstruction. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open ShiftlessDecomposition

def PreparedDenominator.flat (p : PreparedDenominator) : List PreparedOccurrence :=
  p.groups.toList.flatMap (fun g => g.occurrences.toList)

def decompositionPowers (d : Array (ShiftlessDecomposition.Group ℚ)) : List (Polynomial ℚ) :=
  d.toList.flatMap (fun g => g.occurrences.toList.map
    (fun o => taylor (o.shift : ℚ) g.base ^ o.multiplicity))

theorem prepare_powers (D : Polynomial ℚ) (d : Array (ShiftlessDecomposition.Group ℚ)) :
    ((prepare D d).flat.map (·.power)) = decompositionPowers d := by
  simp [PreparedDenominator.flat, prepare_eq_model, Model.prepareGroup,
    Model.prepareOccurrence, decompositionPowers, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]

theorem powers_pairwise {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d) :
    (decompositionPowers d).Pairwise IsCoprime := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro g hg
    have hv := hd.groups_valid g (by simpa using hg)
    apply List.pairwise_map.mpr
    apply hv.increasing.imp
    intro a b hab
    have hc := shift_coprime (hv.shiftFree (b.shift - a.shift) (by omega)) a.shift
    have hh : (a.shift : ℚ) + ((b.shift - a.shift : ℤ) : ℚ) = (b.shift : ℚ) := by
      push_cast
      ring
    simp only [taylor_taylor, hh] at hc
    exact hc.pow
  · apply hd.separated.imp
    intro a b hab x hx y hy
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    have hc := shift_coprime (hab (v.shift - o.shift)) o.shift
    have hh : (o.shift : ℚ) + ((v.shift - o.shift : ℤ) : ℚ) = (v.shift : ℚ) := by
      push_cast
      ring
    simp only [taylor_taylor, hh] at hc
    exact hc.pow

private theorem prod_flatMap {A B : Type*} [CommMonoid B] (l : List A) (f : A → List B) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih]

private theorem sum_flatMap {A B : Type*} [AddCommMonoid B] (l : List A) (f : A → List B) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih]

theorem powers_prod {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d) :
    (decompositionPowers d).prod = C D.leadingCoeff⁻¹ * D := by
  have hr := hd.reconstruct
  have hc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd.nonzero
  have he := congrArg (fun x => C D.leadingCoeff⁻¹ * x) hr
  calc
    _ = (d.map Group.expand).prod := by
      simp only [decompositionPowers, prod_flatMap, ← Array.prod_toList, Array.toList_map]
      congr 1
      apply List.map_congr_left
      intro g hg
      simp [Group.expand, ← Array.prod_toList]
    _ = _ := by simpa [← mul_assoc, ← C_mul, hc] using he

theorem prepare_flat_inverse (D : Polynomial ℚ) (d : Array (ShiftlessDecomposition.Group ℚ))
    (o : PreparedOccurrence) (ho : o ∈ (prepare D d).flat) :
    o.inverse = inverseMod ((C D.leadingCoeff⁻¹ * D) / o.power) o.power := by
  simp only [PreparedDenominator.flat, prepare_eq_model, Array.toList_map,
    List.flatMap_map, List.mem_flatMap] at ho
  obtain ⟨g, hg, ho⟩ := ho
  simp only [Model.prepareGroup, Array.toList_map, List.mem_map] at ho
  obtain ⟨a, ha, rfl⟩ := ho
  rfl

private theorem list_prod_map_eq_fin {A B : Type*} [CommMonoid B] (l : List A) (f : A → B) :
    (l.map f).prod = ∏ i : Fin l.length, f l[i.val] := by
  simp

private theorem list_sum_map_eq_fin {A B : Type*} [AddCommMonoid B] (l : List A) (f : A → B) :
    (l.map f).sum = ∑ i : Fin l.length, f l[i.val] := by
  simp

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem prepared_partialFractions {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (N : Polynomial K)
    (hN : N.degree < ((prepare D d).monicDenominator.map (algebraMap ℚ K)).degree) :
    (N : RatFunc K) / ((prepare D d).monicDenominator.map (algebraMap ℚ K) : RatFunc K) =
      ((prepare D d).groups.toList.map (groupFraction N)).sum := by
  classical
  let p := prepare D d
  let l := p.flat
  let F := fun i : Fin l.length => l[i.val].power
  let U := fun i : Fin l.length => l[i.val].inverse
  have hm (i) : (F i).Monic := by
    have ho : l[i.val] ∈ p.flat := List.getElem_mem _
    obtain ⟨g, hg, ho⟩ := List.mem_flatMap.mp ho
    exact (prepare_monic hd).factors g (by simpa using hg) _ (by simpa using ho) |>.2
  have hc : Pairwise (fun i j => IsCoprime (F i) (F j)) := by
    have hp : (l.map (·.power)).Pairwise IsCoprime := by
      simpa [l, p, prepare_powers] using powers_pairwise hd
    have h := List.pairwise_map.mp hp
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact h.rel_getElem_of_lt i.isLt j.isLt hij
    · exact (h.rel_getElem_of_lt j.isLt i.isLt hij).symm
  have hprod : ∏ i, F i = p.monicDenominator := by
    have h := powers_prod hd
    rw [← prepare_powers D d] at h
    rw [list_prod_map_eq_fin] at h
    calc
      (∏ i, F i) = C D.leadingCoeff⁻¹ * D := h
      _ = p.monicDenominator := by simp [p, prepare_eq_model]
  let E := fun i => ∏ j ∈ Finset.univ.erase i, F j
  have hco (i) : p.monicDenominator / F i = E i := by
    rw [← hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (F i)]
    exact mul_div_cancel_right₀ _ (hm i).ne_zero
  have hu (i) : F i ∣ E i * U i - 1 := by
    have hinv := prepare_flat_inverse D d l[i.val] (List.getElem_mem _)
    have hc' : IsCoprime (E i) (F i) :=
      IsCoprime.prod_left (fun j hj => hc (Finset.mem_erase.mp hj).1)
    have h := inverseMod_spec (E i) (F i) hc'
    change U i = _ at hinv
    have hden : C D.leadingCoeff⁻¹ * D = p.monicDenominator := by
      simp [p, prepare_eq_model]
    rw [hden, hco] at hinv
    simpa only [hinv] using h
  have hprodK : ∏ i, (F i).map (algebraMap ℚ K) = p.monicDenominator.map (algebraMap ℚ K) := by
    rw [← hprod, Polynomial.map_prod]
  have huK (i) : (F i).map (algebraMap ℚ K) ∣
      (∏ j ∈ Finset.univ.erase i, (F j).map (algebraMap ℚ K)) * (U i).map (algebraMap ℚ K) - 1 := by
    have hd := (Polynomial.mapRingHom (algebraMap ℚ K)).map_dvd (hu i)
    change (F i).map (algebraMap ℚ K) ∣ (E i * U i - 1).map (algebraMap ℚ K) at hd
    simpa [E, Polynomial.map_prod] using hd
  have h := partialFractions_fraction
    (fun i => (F i).map (algebraMap ℚ K)) (fun i => (U i).map (algebraMap ℚ K))
    (fun i => (hm i).map _) (fun i j hij => (hc hij).map (Polynomial.mapRingHom (algebraMap ℚ K))) huK N
    (by simpa only [hprodK] using hN)
  rw [hprodK] at h
  convert h using 1
  change ((p.groups.toList.map fun g =>
    (g.occurrences.toList.map (occurrenceFraction N)).sum).sum) = _
  rw [← sum_flatMap]
  rw [← List.map_flatMap]
  exact list_sum_map_eq_fin l (occurrenceFraction N)

end Gosper.RationalSum
