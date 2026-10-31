module

public import SympyProofs.Sum.RationalSum.Reduction
public import SympyProofs.Sum.RationalSum.Obstruction

/-! Degree and denominator invariants of the computed residual arrays. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Each coefficient in a residual is proper relative to its base. -/
def Residual.Proper (r : Residual K) : Prop :=
  ∀ a ∈ r.numerators, a.degree < (r.base.map (algebraMap ℚ K)).degree

namespace Model

theorem digit_proper (g : PreparedGroup) (o : PreparedOccurrence)
    (hf : o.factor = taylor (o.shift : ℚ) g.base) (hm : g.base.Monic)
    (s : Array (ShiftSum K) × Array (Polynomial K) × Polynomial K) (j : ℕ)
    (hs : (Residual.mk g.base s.2.1).Proper) :
    (Residual.mk g.base (digit g o s j).2.1).Proper := by
  have hd : (taylor ((-o.shift : ℤ) : K)
      (s.2.2 %ₘ o.factor.map (algebraMap ℚ K))).degree <
      (g.base.map (algebraMap ℚ K)).degree := by
    rw [degree_taylor]
    have hm' : o.factor.Monic := by rw [hf]; simpa [Monic] using hm
    have h := degree_modByMonic_lt s.2.2 (hm'.map (algebraMap ℚ K))
    simpa only [hf, map_taylor, degree_taylor] using h
  have hmod : (Residual.mk g.base (s.2.1.modify (o.multiplicity - j - 1)
      (· + taylor ((-o.shift : ℤ) : K) (s.2.2 %ₘ o.factor.map (algebraMap ℚ K))))).Proper := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
    simp only [Array.size_modify] at hi
    rw [Array.getElem_modify]
    split
    · exact (degree_add_le _ _).trans_lt (max_lt (hs _ (Array.getElem_mem _)) hd)
    · exact hs _ (Array.getElem_mem _)
  unfold digit
  split <;> exact hmod

theorem occurrence_proper (N : Polynomial K) (g : PreparedGroup) (o : PreparedOccurrence)
    (hf : o.factor = taylor (o.shift : ℚ) g.base) (hm : g.base.Monic)
    (s : Array (ShiftSum K) × Array (Polynomial K))
    (hs : (Residual.mk g.base s.2).Proper) :
    (Residual.mk g.base (occurrence N g s o).2).Proper := by
  unfold occurrence
  have hi (l : List ℕ) (s : Array (ShiftSum K) × Array (Polynomial K) × Polynomial K)
      (hs : (Residual.mk g.base s.2.1).Proper) :
      (Residual.mk g.base (l.foldl (digit g o) s).2.1).Proper := by
    induction l generalizing s with
    | nil => exact hs
    | cons j js ih => exact ih _ (digit_proper g o hf hm s j hs)
  exact hi _ _ hs

theorem group_proper (N : Polynomial K) (g : PreparedGroup) (hg : g.Valid)
    (s : Array (ShiftSum K) × Array (Residual K)) :
    ∃ r : Residual K, (group N s g).2 = s.2.push r ∧ r.base = g.base ∧ r.Proper := by
  have hi (l : List PreparedOccurrence) (hl : ∀ o ∈ l, o ∈ g.occurrences)
      (s : Array (ShiftSum K) × Array (Polynomial K))
      (hs : (Residual.mk g.base s.2).Proper) :
      (Residual.mk g.base (l.foldl (occurrence N g) s).2).Proper := by
    induction l generalizing s with
    | nil => exact hs
    | cons o os ih =>
      exact ih (fun v hv => hl v (by simp [hv])) _
        (occurrence_proper N g o (hg.occurrences o (hl o (by simp))).1 hg.monic s hs)
  refine ⟨_, rfl, rfl, hi g.occurrences.toList (by simp) _ ?_⟩
  intro a ha
  have hz : a = 0 := (Array.mem_replicate.mp ha).2
  subst a
  simpa using (WithBot.bot_lt_iff_ne_bot.mpr
    (degree_ne_bot.mpr (hg.monic.map (algebraMap ℚ K)).ne_zero))

theorem groups_proper (N : Polynomial K) (l : List PreparedGroup)
    (hl : ∀ g ∈ l, g.Valid) (s : Array (ShiftSum K) × Array (Residual K))
    (hs : ∀ r ∈ s.2, r.Proper) :
    ∀ r ∈ (l.foldl (group N) s).2, r.Proper := by
  induction l generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    obtain ⟨r, he, hb, hr⟩ := group_proper N g (hl g (by simp)) s
    apply ih (fun g hg => hl g (by simp [hg]))
    rw [he]
    intro a ha
    rcases Array.mem_push.mp ha with ha | rfl
    · exact hs a ha
    · exact hr

theorem groups_bases (N : Polynomial K) (l : List PreparedGroup)
    (s : Array (ShiftSum K) × Array (Residual K)) :
    ((l.foldl (group N) s).2.toList.map (·.base)) =
      s.2.toList.map (·.base) ++ l.map (·.base) := by
  induction l generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [group, List.append_assoc]

end Model

theorem model_residual_proper  {D : Polynomial ℚ}
    {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial K) :
    ∀ r ∈ (Model.result (prepare D d) P).residual, r.Proper := by
  exact Model.groups_proper _ _ (fun g hg => prepare_groups_valid hd g (by simpa using hg))
    (#[], #[]) (by simp)

theorem model_residual_bases  (D : Polynomial ℚ)
    (d : Array (ShiftlessDecomposition.Group ℚ)) (P : Polynomial K) :
    ((Model.result (prepare D d) P).residual.toList.map (·.base)) =
      d.toList.map (·.base) := by
  change ((List.foldl (Model.group _) (#[], #[]) _).2.toList.map (·.base)) = _
  rw [Model.groups_bases]
  simp [prepare_eq_model, Model.prepareGroup, List.map_map]

/-- The residual bases inherit exactly the separation of the decomposition. -/
theorem model_residual_separated  {D : Polynomial ℚ}
    {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial K) :
    (Model.result (prepare D d) P).residual.toList.Pairwise
      (fun a b => ShiftlessDecomposition.ShiftCoprime a.base b.base) := by
  rw [← List.pairwise_map (f := Residual.base), model_residual_bases]
  exact List.pairwise_map.mpr hd.separated

theorem model_residual_base_valid  {D : Polynomial ℚ}
    {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial K)
    (r : Residual K) (hr : r ∈ (Model.result (prepare D d) P).residual) :
    r.base.Monic ∧ ShiftlessDecomposition.ShiftFree r.base := by
  have hb : r.base ∈ d.toList.map (·.base) := by
    rw [← model_residual_bases D d P]
    exact List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hb
  have hv := hd.groups_valid g (by simpa using hg)
  exact he ▸ ⟨hv.monic, hv.shiftFree⟩

/-- A proper residual supported on separated shift-free bases is a rational
difference only when every numerator in the representation is zero. -/
theorem residualVanishes_of_summable (r : Result K)
    (hm : ∀ a ∈ r.residual, a.base.Monic)
    (hs : ∀ a ∈ r.residual, ShiftlessDecomposition.ShiftFree a.base)
    (hc : r.residual.toList.Pairwise
      (fun a b => ShiftlessDecomposition.ShiftCoprime a.base b.base))
    (hp : ∀ a ∈ r.residual, a.Proper)
    (h : ∃ G : RatFunc K, Gosper.rationalShift 1 G - G = r.residualPart) :
    r.residualVanishes := by
  classical
  let : CharZero K := ⟨fun m n h => Nat.cast_injective
    ((algebraMap ℚ K).injective (by simpa using h) : (m : ℚ) = n)⟩
  let l := r.residual.toList
  let b := fun i : Fin l.length => l[i.val].base.map (algebraMap ℚ K)
  let n := fun i : Fin l.length => l[i.val].numerators.size
  let a := fun (i : Fin l.length) (j : Fin (n i)) => l[i.val].numerators[j.val]
  let F := fun i => b i ^ n i
  let A := fun i => powerNumerator (b i) (a i)
  have hmem (i : Fin l.length) : l[i.val] ∈ r.residual := by
    simp [l]
  have hb (i) : (b i).Monic := (hm _ (hmem i)).map _
  have ha (i) (j) : (a i j).degree < (b i).degree := hp _ (hmem i) _ (Array.getElem_mem _)
  have hcross (i j : Fin l.length) (hij : i ≠ j) (z : ℤ) :
      IsCoprime (b i) (taylor (z : K) (b j)) := by
    have hc' : ShiftlessDecomposition.ShiftCoprime l[i.val].base l[j.val].base := by
      rcases lt_or_gt_of_ne hij with hij | hij
      · exact hc.rel_getElem_of_lt i.isLt j.isLt hij
      · exact (hc.rel_getElem_of_lt j.isLt i.isLt hij).symm
    have hm := (hc' z).map (Polynomial.mapRingHom (algebraMap ℚ K))
    simpa [b, map_taylor] using hm
  have hself (i : Fin l.length) (z : ℤ) (hz : z ≠ 0) :
      IsCoprime (b i) (taylor (z : K) (b i)) := by
    have h := (hs _ (hmem i) z hz).map (Polynomial.mapRingHom (algebraMap ℚ K))
    simpa [b, map_taylor] using h
  have hF : ShiftlessDecomposition.ShiftFree (∏ i, F i) := by
    intro z hz
    have he : taylor (z : K) (∏ i, F i) = ∏ i, taylor (z : K) (F i) :=
      map_prod (taylorAlgHom (z : K)) F Finset.univ
    rw [he]
    apply IsCoprime.prod_left
    intro i _
    apply IsCoprime.prod_right
    intro j _
    simp only [F, taylor_pow]
    by_cases hij : i = j
    · subst j; exact (hself i z hz).pow
    · exact (hcross i j hij z).pow
  have hsum : r.residualPart = ∑ i, (A i : RatFunc K) / (F i : RatFunc K) := by
    have hv (i : Fin l.length) : l[i.val].expand = (A i : RatFunc K) / (F i : RatFunc K) := by
      simpa only [A, F, a, b, n, Residual.expand, RatFunc.coePolynomial, map_pow] using
        (powerNumerator_fraction (b i) (hb i).ne_zero (a i)).symm
    change (r.residual.map Residual.expand).sum = _
    rw [← Array.sum_toList, Array.toList_map]
    change (l.map Residual.expand).sum = _
    simpa only [hv] using (show (l.map Residual.expand).sum =
      ∑ i : Fin l.length, l[i.val].expand by simp)
  have hzero : ∀ i, A i = 0 := fractions_eq_zero_of_summable F A
    (fun i => (hb i).pow _)
    (fun i j hij => by simpa using (hcross i j hij 0).pow (m := n i) (n := n j))
    hF (fun i => powerNumerator_degree _ (hb i) _ (ha i)) (by simpa only [hsum] using h)
  intro g hg v hv
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (show g ∈ l by simpa [l] using hg)
  subst g
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hv
  exact powerNumerator_eq_zero _ (hb ⟨i, hi⟩) _ (ha ⟨i, hi⟩) (hzero ⟨i, hi⟩) ⟨j, hj⟩

end Gosper.RationalSum
