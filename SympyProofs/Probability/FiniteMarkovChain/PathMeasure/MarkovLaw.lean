module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Marginals
public import SympyProofs.Probability.FiniteMarkovChain.Process.Transition

/-!
# Markov finite-dimensional distributions

For strictly increasing observation times, the coordinate process has the
usual sequential Markov law: draw the initial state from `p`, then draw each
new state using only the previous state and the elapsed time. This is a
finite-dimensional formulation of the Markov property; no division by the
probability of a possibly null history is required.

For a generator, the coordinate process under the path measure is a
time-homogeneous Markov process whose transition probabilities are the transition
matrices. These are `pathMeasure_isHomogeneousMarkovProcess` and
`pathMeasure_hasTransition`.

The sampling law is stated for an increasing list of times. The Markov property in
`Process.MarkovProperty` is stated for a finite set of earlier times.
`pathMeasure_markovPropertyProduct` passes from one to the other by listing the set in
increasing order.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

variable {ι : Type*}

/-- Observe a path at a finite ordered list of times. -/
def observations (ts : List ℝ≥0) (ω : Path ι) : List ι := ts.map ω

private theorem observations_update (t : ℝ≥0) (ts : List ℝ≥0) (ht : t ∉ ts)
    (ω : Path ι) (j : ι) :
    observations (t :: ts) (Function.update ω t j) = j :: observations ts ω := by
  simp only [observations, List.map_cons, Function.update_self]
  congr 1
  apply List.map_congr_left
  intro u hu
  exact Function.update_of_ne (show u ≠ t from fun h => ht (h ▸ hu)) _ _

variable [Fintype ι] [DecidableEq ι]

section Sampling

variable (Q : Matrix ι ι ℝ) (d : ι)

/-- Sequential Markov sampling of states at the listed times. -/
noncomputable def sampleStates (s : ℝ≥0) (i : ι) : List ℝ≥0 → PMF (List ι)
  | [] => PMF.pure []
  | t :: ts => (step Q (t - s) i).bind fun j =>
      (sampleStates t j ts).map (List.cons j)

/-- The mass of a state sequence factors into one transition and the remaining law. -/
theorem sampleStates_cons (s t : ℝ≥0) (i j : ι) (ts : List ℝ≥0) (xs : List ι) :
    sampleStates Q s i (t :: ts) (j :: xs) =
      step Q (t - s) i j * sampleStates Q t j ts xs := by
  rw [sampleStates, PMF.bind_apply, tsum_eq_single j]
  · congr 1
    simp [PMF.map_apply]
  · intro a ha
    simp [PMF.map_apply, Ne.symm ha]

/-- Appending an observation multiplies the history probability by the transition
from its last state. -/
theorem sampleStates_append_one (s t : ℝ≥0) (i j : ι) (ts : List ℝ≥0) (xs : List ι)
    (hlen : ts.length = xs.length) :
    sampleStates Q s i (ts ++ [t]) (xs ++ [j]) =
      sampleStates Q s i ts xs * step Q (t - ts.getLastD s) (xs.getLastD i) j := by
  induction ts generalizing s i xs with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst xs
    rw [List.nil_append, List.nil_append, sampleStates_cons]
    simp only [List.getLastD_nil, sampleStates, PMF.pure_apply_self, mul_one, one_mul]
  | cons u us ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, sampleStates_cons]
      rw [ih u x xs hlen]
      simp only [List.getLastD_cons, mul_assoc]

theorem sampleFuture_observations (s : ℝ≥0) (i : ι) (ts : List ℝ≥0) (hnd : ts.Nodup) :
    (sampleFuture Q d s i ts).map (observations ts) = sampleStates Q s i ts := by
  induction ts generalizing s i with
  | nil => simp [sampleFuture, sampleStates, observations, PMF.pure_map]
  | cons t ts ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnd
    simp only [sampleFuture, sampleStates, PMF.map_bind, PMF.map_comp]
    congr 1
    funext j
    have he : observations (t :: ts) ∘ (fun ω => Function.update ω t j) =
        List.cons j ∘ observations ts := by
      funext ω
      exact observations_update t ts ht ω j
    rw [he, ← PMF.map_comp, ih t j hnd]

theorem sampledPath_observations (p : PMF ι) (ts : List ℝ≥0)
    (ho : ts.SortedLT) :
    (sampledPath Q d p ts.toFinset).map (observations ts) =
      p.bind (fun i => sampleStates Q 0 i ts) := by
  have hnd : ts.Nodup := ho.nodup
  have hsort : ts.toFinset.sort (· ≤ ·) = ts :=
    (List.toFinset_sort (· ≤ ·) hnd).mpr ho.sortedLE.pairwise
  simp only [sampledPath, hsort, PMF.map_bind]
  congr 1
  funext i
  exact sampleFuture_observations Q d 0 i ts hnd

end Sampling

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

-- State lists carry the discrete sigma-algebra.
local instance : MeasurableSpace (List ι) := ⊤

section Observations

variable (Q : Matrix ι ι ℝ) (d : ι)

/-- The probability of a finite observed history at strictly increasing times is given
by the Markov sampling law. In particular each transition depends only on the last
state. -/
theorem pathMeasure_observations_eq (p : PMF ι) (ts : List ℝ≥0)
    (ho : ts.SortedLT) (xs : List ι) :
    pathMeasure Q d p {ω | observations ts ω = xs} =
      (p.bind (fun i => sampleStates Q 0 i ts)) xs := by
  let I := ts.toFinset
  let f : (I → ι) → List ι := fun x =>
    ts.attach.map (fun t => x ⟨t.1, List.mem_toFinset.mpr t.2⟩)
  have hf : Measurable f := measurable_of_countable f
  have he : f ∘ I.restrict = observations ts := by
    funext ω
    simp [f, Finset.restrict, observations]
  have hm : Measurable (observations (ι := ι) ts) :=
    he ▸ hf.comp (Finset.measurable_restrict I)
  have h := congrArg (Measure.map f) (pathMeasure_isProjectiveLimit Q d p I)
  rw [Measure.map_map hf (Finset.measurable_restrict I), he,
    PMF.toMeasure_map _ _ hf] at h
  change pathMeasure Q d p (observations ts ⁻¹' {xs}) = _
  rw [← Measure.map_apply hm (measurableSet_singleton xs), h,
    PMF.toMeasure_apply_singleton _ xs (measurableSet_singleton xs)]
  congr 1
  rw [finiteLaw, PMF.map_comp, he]
  exact sampledPath_observations Q d p ts ho

end Observations

variable {Q : Matrix ι ι ℝ}

/-- After any observed history ending in state `i` at time `s`, the path measure
gives state `j` at time `t` the probability `transition Q (t - s) i j`. -/
private theorem pathMeasure_history_step (hQ : IsGenerator Q) (d : ι) (p : PMF ι)
    (ts : List ℝ≥0) (xs : List ι) (s t : ℝ≥0) (i j : ι) (ho : (ts ++ [s, t]).SortedLT)
    (hlen : ts.length = xs.length) :
    pathMeasure Q d p {ω | observations (ts ++ [s, t]) ω = xs ++ [i, j]} =
      pathMeasure Q d p {ω | observations (ts ++ [s]) ω = xs ++ [i]} *
        ENNReal.ofReal (transition Q (↑(t - s) : ℝ) i j) := by
  have hprefix : (ts ++ [s]).SortedLT :=
    (ho.pairwise.sublist (List.Sublist.append_left (by simp) ts)).sortedLT
  rw [pathMeasure_observations_eq Q d p _ ho,
    pathMeasure_observations_eq Q d p _ hprefix]
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro k
  have hlen' : (ts ++ [s]).length = (xs ++ [i]).length := by simp [hlen]
  have hh := sampleStates_append_one Q 0 t k j (ts ++ [s]) (xs ++ [i]) hlen'
  simpa only [List.append_assoc, List.cons_append, List.nil_append,
    List.getLastD_concat, step_apply hQ, NNReal.coe_sub, mul_assoc] using congrArg (p k * ·) hh

/-- Two-time probabilities, including the probability of the current state. -/
theorem pathMeasure_two_times (hQ : IsGenerator Q) (d : ι) (p : PMF ι)
    (s t : ℝ≥0) (hst : s < t) (i j : ι) :
    pathMeasure Q d p {ω | ω s = i ∧ ω t = j} =
      pathMeasure Q d p {ω | ω s = i} * ENNReal.ofReal (transition Q (↑(t - s) : ℝ) i j) := by
  have h := pathMeasure_history_step hQ d p [] [] s t i j
    (by simp [List.sortedLT_iff_pairwise, hst]) rfl
  simpa [observations] using h

/-- For a generator, the transition probabilities of the coordinate process under the
path measure are the transition matrices. -/
theorem pathMeasure_hasTransition (hQ : IsGenerator Q) (d : ι) (p : PMF ι) :
    HasTransition Q coordinate (pathMeasure Q d p) := by
  intro s t i j
  change pathMeasure Q d p {ω | ω s = i ∧ ω (s + t) = j} =
    pathMeasure Q d p {ω | ω s = i} * _
  rcases eq_or_lt_of_le (zero_le (a := t)) with rfl | ht
  · by_cases hij : i = j
    · subst hij
      simp
    · have e : {ω : Path ι | ω s = i ∧ ω (s + 0) = j} = ∅ := by
        ext ω
        simp only [add_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        exact hij (h1.symm.trans h2)
      rw [e, measure_empty]
      simp [hij]
  · rw [pathMeasure_two_times hQ d p s (s + t) (lt_add_of_pos_right s ht) i j,
      add_tsub_cancel_left]

/-- For a generator, the coordinate process under the path measure has the Markov
property. -/
theorem pathMeasure_markovPropertyProduct (hQ : IsGenerator Q) (d : ι) (p : PMF ι) :
    MarkovPropertyProduct coordinate (pathMeasure Q d p) := by
  intro F x s t i j hF hst
  -- list the earlier times in increasing order
  have hmem : ∀ u, u ∈ F.sort (· ≤ ·) ↔ u ∈ F := fun u => Finset.mem_sort _
  have ho : (F.sort (· ≤ ·) ++ [s, t]).SortedLT :=
    List.sortedLT_iff_pairwise.2 (List.pairwise_append.2
      ⟨F.sortedLT_sort.pairwise, by simp [hst], fun u hu v hv => by
        have hus := hF u ((hmem u).1 hu)
        rcases List.mem_pair.1 hv with rfl | rfl
        · exact hus
        · exact hus.trans hst⟩)
  have hlen : (F.sort (· ≤ ·)).length = ((F.sort (· ≤ ·)).map x).length := by simp
  have hpast : ∀ ω : Path ι, (∀ u ∈ F, ω u = x u) ↔
      (F.sort (· ≤ ·)).map ω = (F.sort (· ≤ ·)).map x := fun ω => by
    rw [List.map_inj_left]
    exact ⟨fun h u hu => h u ((hmem u).1 hu), fun h u hu => h u ((hmem u).2 hu)⟩
  have e1 : {ω : Path ι | (∀ u ∈ F, coordinate u ω = x u) ∧ coordinate s ω = i ∧
        coordinate t ω = j} =
      {ω | observations (F.sort (· ≤ ·) ++ [s, t]) ω = (F.sort (· ≤ ·)).map x ++ [i, j]} := by
    ext ω
    change ((∀ u ∈ F, ω u = x u) ∧ ω s = i ∧ ω t = j) ↔
      (F.sort (· ≤ ·) ++ [s, t]).map ω = (F.sort (· ≤ ·)).map x ++ [i, j]
    rw [hpast ω, List.map_append]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [h1, List.map_cons, List.map_cons, List.map_nil, h2, h3]
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
      exact ⟨h1, h2.1, h2.2⟩
  have e2 : {ω : Path ι | (∀ u ∈ F, coordinate u ω = x u) ∧ coordinate s ω = i} =
      {ω | observations (F.sort (· ≤ ·) ++ [s]) ω = (F.sort (· ≤ ·)).map x ++ [i]} := by
    ext ω
    change ((∀ u ∈ F, ω u = x u) ∧ ω s = i) ↔
      (F.sort (· ≤ ·) ++ [s]).map ω = (F.sort (· ≤ ·)).map x ++ [i]
    rw [hpast ω, List.map_append]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, List.map_cons, List.map_nil, h2]
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
      exact ⟨h1, h2⟩
  rw [e1, e2]
  change _ * pathMeasure Q d p {ω | ω s = i} = _ * pathMeasure Q d p {ω | ω s = i ∧ ω t = j}
  rw [pathMeasure_history_step hQ d p _ _ s t i j ho hlen,
    pathMeasure_two_times hQ d p s t hst i j]
  ring

/-- For a generator, the coordinate process under the path measure is a
time-homogeneous Markov process. -/
theorem pathMeasure_isHomogeneousMarkovProcess (hQ : IsGenerator Q) (d : ι) (p : PMF ι) :
    IsHomogeneousMarkovProcess coordinate (pathMeasure Q d p) :=
  (pathMeasure_hasTransition hQ d p).isHomogeneousMarkovProcess measurable_coordinate
    (pathMeasure_markovPropertyProduct hQ d p)

end SympyProofs.FiniteMarkovChain
