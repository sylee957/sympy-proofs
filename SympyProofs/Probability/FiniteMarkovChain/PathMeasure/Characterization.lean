module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.MarkovLaw

/-!
# The path measure is the unique law of the chain

Fix a generator `Q` and an initial distribution `p`. Exactly one measure on paths
makes the coordinate process start from `p`, be a time-homogeneous Markov process, and
have the transition probabilities of `Q`. This is `existsUnique_pathMeasure`, and
`eq_pathMeasure_iff` shows that the measure is `pathMeasure Q d p`.

So the path measure is determined by the chain it describes and not by how it was
constructed. In particular it does not depend on the filler state `d`, which is
`pathMeasure_filler`.

`chainLaw hQ p` names that one measure without the construction: it is defined as the
measure that `existsUnique_pathMeasure` says exists. It needs the proof `hQ` that `Q` is
a generator, and it mentions no filler state. It equals `pathMeasure Q d p` for every
`d`, by `chainLaw_eq_pathMeasure`.

The process itself is not unique. The same chain lives on many probability spaces, and
on one space two different processes can have the same probabilities at every finite
set of times. What is unique is the law on paths.

`IsHomogeneousMarkovProcess.law` and `HasTransition.law` move a process on any
probability space to the space of paths: the coordinate process under its law is again
a time-homogeneous Markov process with the same transition probabilities.

So the uniqueness holds for processes on any probability space. A time-homogeneous
Markov process that starts from `p` and has the transition probabilities of `Q` has
`chainLaw hQ p` as its law on paths, by
`IsHomogeneousMarkovProcess.law_eq_chainLaw`. Two such processes with the same law
at time `0` have the same law on paths, even on different probability spaces, by
`IsHomogeneousMarkovProcess.law_eq`. The second statement needs no generator: any
matrix that gives the transition probabilities of both will do.

The proof compares two measures on the probabilities of finite histories, one time
after another. `HasTransition.step` is the step: after any observed history ending in
state `i` at time `s`, the process is in state `j` at time `t` with probability
`transition Q (t - s) i j`. It is stated for an increasing list of times. The Markov
property in `Process.MarkovProperty` is stated for a finite set of earlier times with a
function that gives the state at each. For distinct times such a function exists, so
the list form follows.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

variable {ι : Type*}

private theorem observations_eq_empty {ts : List ℝ≥0} {xs : List ι}
    (h : ts.length ≠ xs.length) :
    {ω : Path ι | observations ts ω = xs} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro he
  exact h (by rw [← he]; simp [observations])

/-! ### The next state after an observed history -/

/-- For distinct times and as many states, some function sends each time to its
state. -/
private theorem exists_map_eq (i : ι) (ts : List ℝ≥0) (xs : List ι) (hnd : ts.Nodup)
    (hlen : ts.length = xs.length) : ∃ x : ℝ≥0 → ι, ts.map x = xs := by
  induction ts generalizing xs with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hlen.symm
    exact ⟨fun _ => i, hx ▸ rfl⟩
  | cons t ts ih =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnd
      obtain ⟨x, rfl⟩ := ih ys hnd (by simpa using hlen)
      refine ⟨Function.update x t y, ?_⟩
      simp only [List.map_cons, Function.update_self]
      congr 1
      exact List.map_congr_left fun u hu =>
        Function.update_of_ne (show u ≠ t from fun h => ht (h ▸ hu)) _ _

section

variable [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω] {Q : Matrix ι ι ℝ}
  {X : ℝ≥0 → Ω → ι} {P : Measure Ω}

/-- After any observed history ending in state `i` at time `s`, the process is in
state `j` at time `t` with probability `transition Q (t - s) i j`. -/
theorem HasTransition.step [IsFiniteMeasure P] (ht : HasTransition Q X P)
    (hm : MarkovPropertyProduct X P) (ts : List ℝ≥0) (xs : List ι) (s t : ℝ≥0)
    (i j : ι) (ho : (ts ++ [s, t]).SortedLT) (hlen : ts.length = xs.length) :
    P {ω | (ts ++ [s, t]).map (fun u => X u ω) = xs ++ [i, j]} =
      P {ω | (ts ++ [s]).map (fun u => X u ω) = xs ++ [i]} *
        ENNReal.ofReal (transition Q (↑(t - s) : ℝ) i j) := by
  have hp := List.pairwise_append.1 ho.pairwise
  have hst : s < t := by simpa using hp.2.1
  have hts : ∀ u ∈ ts, u < s := fun u hu => hp.2.2 u hu s (by simp)
  -- write the observed states as a function of the time
  obtain ⟨x, rfl⟩ := exists_map_eq i ts xs (hp.1.imp ne_of_lt) hlen
  have e1 : {ω | (ts ++ [s, t]).map (fun u => X u ω) = ts.map x ++ [i, j]} =
      {ω | (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} := by
    ext ω
    change (ts ++ [s, t]).map (fun u => X u ω) = ts.map x ++ [i, j] ↔
      (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i ∧ X t ω = j
    rw [List.map_append]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
      exact ⟨fun u hu => List.map_inj_left.1 h1 u (List.mem_toFinset.1 hu), h2.1, h2.2⟩
    · rintro ⟨h1, h2, h3⟩
      rw [List.map_inj_left.2 fun u hu => h1 u (List.mem_toFinset.2 hu)]
      simp [h2, h3]
  have e2 : {ω | (ts ++ [s]).map (fun u => X u ω) = ts.map x ++ [i]} =
      {ω | (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i} := by
    ext ω
    change (ts ++ [s]).map (fun u => X u ω) = ts.map x ++ [i] ↔
      (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i
    rw [List.map_append]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
      exact ⟨fun u hu => List.map_inj_left.1 h1 u (List.mem_toFinset.1 hu), h2⟩
    · rintro ⟨h1, h2⟩
      rw [List.map_inj_left.2 fun u hu => h1 u (List.mem_toFinset.2 hu)]
      simp [h2]
  rw [e1, e2]
  have hmk := hm ts.toFinset x s t i j (fun u hu => hts u (List.mem_toFinset.1 hu)) hst
  have h2 := ht s (t - s) i j
  rw [add_tsub_cancel_of_le hst.le] at h2
  rw [h2] at hmk
  by_cases hm0 : P {ω | X s ω = i} = 0
  · have hA : P {ω | (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} = 0 :=
      measure_mono_null (fun ω hω => hω.2.1) hm0
    have hB : P {ω | (∀ u ∈ ts.toFinset, X u ω = x u) ∧ X s ω = i} = 0 :=
      measure_mono_null (fun ω hω => hω.2) hm0
    rw [hA, hB, zero_mul]
  · refine (ENNReal.mul_left_inj hm0 (measure_ne_top P _)).1 ?_
    rw [hmk]
    ring

end

/-! ### Processes on other probability spaces -/

section

open Filter Topology

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {Ω : Type*} [MeasurableSpace Ω]

/-- If a process is a time-homogeneous Markov process, then so is the coordinate
process under its law. -/
theorem IsHomogeneousMarkovProcess.law {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
    (h : IsHomogeneousMarkovProcess X P) :
    IsHomogeneousMarkovProcess coordinate (P.map fun ω t => X t ω) := by
  have hΦ : Measurable fun ω (t : ℝ≥0) => X t ω := Measurable.of_eval h.measurable
  have h1 : ∀ (s : ℝ≥0) (i : ι), MeasurableSet {ω : Path ι | ω s = i} := fun s i =>
    measurable_coordinate s (measurableSet_singleton i)
  have h2 : ∀ (s t : ℝ≥0) (i j : ι), MeasurableSet {ω : Path ι | ω s = i ∧ ω t = j} :=
    fun s t i j => (h1 s i).inter (h1 t j)
  have h3 : ∀ (F : Finset ℝ≥0) (x : ℝ≥0 → ι),
      MeasurableSet {ω : Path ι | ∀ u ∈ F, ω u = x u} := fun F x => by
    have e : {ω : Path ι | ∀ u ∈ F, ω u = x u} = ⋂ u ∈ F, {ω | ω u = x u} := by
      ext ω
      simp
    rw [e]
    exact Finset.measurableSet_biInter F fun u _ => h1 u (x u)
  have h4 : ∀ (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s : ℝ≥0) (i : ι),
      MeasurableSet {ω : Path ι | (∀ u ∈ F, ω u = x u) ∧ ω s = i} :=
    fun F x s i => (h3 F x).inter (h1 s i)
  have h5 : ∀ (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s t : ℝ≥0) (i j : ι),
      MeasurableSet {ω : Path ι | (∀ u ∈ F, ω u = x u) ∧ ω s = i ∧ ω t = j} :=
    fun F x s t i j => (h3 F x).inter (h2 s t i j)
  set μ := P.map fun ω t => X t ω with hμ
  refine ⟨measurable_coordinate, fun F x s t i j hF hst => ?_, fun s s' d i j => ?_,
    fun s i => ?_⟩
  · change μ {ω | (∀ u ∈ F, ω u = x u) ∧ ω s = i ∧ ω t = j} * μ {ω | ω s = i} =
      μ {ω | (∀ u ∈ F, ω u = x u) ∧ ω s = i} * μ {ω | ω s = i ∧ ω t = j}
    rw [hμ, Measure.map_apply hΦ (h5 F x s t i j), Measure.map_apply hΦ (h1 s i),
      Measure.map_apply hΦ (h4 F x s i), Measure.map_apply hΦ (h2 s t i j)]
    exact h.markov F x s t i j hF hst
  · change μ {ω | ω s = i ∧ ω (s + d) = j} * μ {ω | ω s' = i} =
      μ {ω | ω s' = i ∧ ω (s' + d) = j} * μ {ω | ω s = i}
    rw [hμ, Measure.map_apply hΦ (h2 s (s + d) i j), Measure.map_apply hΦ (h1 s' i),
      Measure.map_apply hΦ (h2 s' (s' + d) i j), Measure.map_apply hΦ (h1 s i)]
    exact h.homogeneous s s' d i j
  · change Tendsto (fun d : ℝ≥0 => μ {ω | ω s = i ∧ ω (s + d) = i}) (𝓝 0)
      (𝓝 (μ {ω | ω s = i}))
    simp_rw [hμ, Measure.map_apply hΦ (h2 s _ i i), Measure.map_apply hΦ (h1 s i)]
    exact h.continuous s i

/-- If a process has the transition probabilities of a matrix, then so does the
coordinate process under its law. -/
theorem HasTransition.law [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    {X : ℝ≥0 → Ω → ι} {P : Measure Ω} (hX : ∀ t, Measurable (X t))
    (ht : HasTransition Q X P) : HasTransition Q coordinate (P.map fun ω u => X u ω) := by
  have hΦ : Measurable fun ω (u : ℝ≥0) => X u ω := Measurable.of_eval hX
  have h1 : ∀ (s : ℝ≥0) (i : ι), MeasurableSet {ω : Path ι | ω s = i} := fun s i =>
    measurable_coordinate s (measurableSet_singleton i)
  have h2 : ∀ (s t : ℝ≥0) (i j : ι), MeasurableSet {ω : Path ι | ω s = i ∧ ω t = j} :=
    fun s t i j => (h1 s i).inter (h1 t j)
  intro s t i j
  change (P.map fun ω u => X u ω) {ω | ω s = i ∧ ω (s + t) = j} =
    (P.map fun ω u => X u ω) {ω | ω s = i} * _
  rw [Measure.map_apply hΦ (h2 s (s + t) i j), Measure.map_apply hΦ (h1 s i)]
  exact ht s t i j

end

/-! ### Uniqueness of the law -/

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A finite measure on paths is determined by the probabilities of finite histories. -/
theorem measure_ext_observations {μ ν : Measure (Path ι)} [IsFiniteMeasure ν]
    (h : ∀ ts : List ℝ≥0, ts.SortedLT → ∀ xs : List ι,
      μ {ω | observations ts ω = xs} = ν {ω | observations ts ω = xs}) : μ = ν := by
  refine IsProjectiveLimit.unique (P := fun I : Finset ℝ≥0 => ν.map I.restrict)
    (fun I => ?_) (fun I => rfl)
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton x),
    Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton x)]
  have hs : (I.restrict ⁻¹' {x} : Set (Path ι)) =
      {ω | observations (I.sort (· ≤ ·)) ω =
        (I.sort (· ≤ ·)).attach.map (fun t => x ⟨t.1, (Finset.mem_sort _).1 t.2⟩)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, observations]
    constructor
    · rintro rfl
      simp [Finset.restrict]
    · intro he
      funext t
      have ht : t.1 ∈ I.sort (· ≤ ·) := (Finset.mem_sort _).2 t.2
      have he' : (I.sort (· ≤ ·)).attach.map (fun u => ω u.1) =
          (I.sort (· ≤ ·)).attach.map (fun u => x ⟨u.1, (Finset.mem_sort _).1 u.2⟩) := by
        rw [← he]; simp
      exact List.map_inj_left.1 he' ⟨t.1, ht⟩ (List.mem_attach _ _)
  rw [hs]
  exact h _ (Finset.sortedLT_sort I) _

variable [DecidableEq ι] {Q : Matrix ι ι ℝ}

private theorem measure_coordinate_eq_sum {μ : Measure (Path ι)}
    (ht : HasTransition Q coordinate μ) (t : ℝ≥0) (j : ι) :
    μ {ω | ω t = j} =
      ∑ i, μ {ω | ω 0 = i} * ENNReal.ofReal (transition Q (t : ℝ) i j) := by
  have hu : {ω : Path ι | ω t = j} = ⋃ i, {ω : Path ι | ω 0 = i ∧ ω t = j} := by
    ext ω; simp
  have hm : ∀ i, MeasurableSet {ω : Path ι | ω 0 = i ∧ ω t = j} := fun i =>
    (measurable_coordinate 0 (measurableSet_singleton i)).inter
      (measurable_coordinate t (measurableSet_singleton j))
  have hd : Pairwise (Function.onFun Disjoint fun i => {ω : Path ι | ω 0 = i ∧ ω t = j}) := by
    intro a b hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_ofPred_eq]
    rintro ω ⟨rfl, -⟩ ⟨h, -⟩
    exact hab h
  rw [hu, measure_iUnion hd hm, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : μ {ω | ω 0 = i ∧ ω (0 + t) = j} =
      μ {ω | ω 0 = i} * ENNReal.ofReal (transition Q (t : ℝ) i j) := ht 0 t i j
  rwa [zero_add] at h

/-- Two measures on paths with the same initial law, under which the coordinate
process is Markov with the transition probabilities of `Q`, give every finite history
the same probability. -/
theorem HasTransition.observations_eq {μ ν : Measure (Path ι)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμt : HasTransition Q coordinate μ)
    (hμm : IsHomogeneousMarkovProcess coordinate μ) (hνt : HasTransition Q coordinate ν)
    (hνm : IsHomogeneousMarkovProcess coordinate ν)
    (h0 : μ.map (coordinate 0) = ν.map (coordinate 0))
    (ts : List ℝ≥0) (ho : ts.SortedLT) (xs : List ι) :
    μ {ω | observations ts ω = xs} = ν {ω | observations ts ω = xs} := by
  by_cases hlen : ts.length = xs.length
  swap
  · rw [observations_eq_empty hlen, measure_empty, measure_empty]
  induction ts using List.reverseRecOn generalizing xs with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst hx
    have hu : {ω : Path ι | observations [] ω = []} = coordinate 0 ⁻¹' Set.univ := by
      ext ω; simp [observations]
    rw [hu, ← Measure.map_apply (measurable_coordinate 0) MeasurableSet.univ,
      ← Measure.map_apply (measurable_coordinate 0) MeasurableSet.univ, h0]
  | append_singleton l t ih =>
    rcases List.eq_nil_or_concat xs with rfl | ⟨ys, j, rfl⟩
    · simp at hlen
    rw [List.concat_eq_append] at hlen ⊢
    have hl : l.length = ys.length := by simpa using hlen
    rcases List.eq_nil_or_concat l with rfl | ⟨l', s, rfl⟩
    · have hy : ys = [] := List.length_eq_zero_iff.mp hl.symm
      subst hy
      have hset : {ω : Path ι | observations ([] ++ [t]) ω = [] ++ [j]} = {ω | ω t = j} := by
        ext ω; simp [observations]
      have hz : ∀ i, μ {ω : Path ι | ω 0 = i} = ν {ω : Path ι | ω 0 = i} := by
        intro i
        have hs : {ω : Path ι | ω 0 = i} = coordinate 0 ⁻¹' {i} := rfl
        rw [hs, ← Measure.map_apply (measurable_coordinate 0) (measurableSet_singleton i),
          ← Measure.map_apply (measurable_coordinate 0) (measurableSet_singleton i), h0]
      rw [hset, measure_coordinate_eq_sum hμt t j, measure_coordinate_eq_sum hνt t j]
      exact Finset.sum_congr rfl fun i _ => by rw [hz i]
    · rcases List.eq_nil_or_concat ys with rfl | ⟨xs', i, rfl⟩
      · simp at hl
      simp only [List.concat_eq_append] at *
      have hl' : l'.length = xs'.length := by simpa using hl
      have ho' : (l' ++ [s, t]).SortedLT := by simpa using ho
      have hprefix : (l' ++ [s]).SortedLT :=
        (ho'.pairwise.sublist (List.Sublist.append_left (by simp) l')).sortedLT
      have e1 : l' ++ [s] ++ [t] = l' ++ [s, t] := by simp
      have e2 : xs' ++ [i] ++ [j] = xs' ++ [i, j] := by simp
      have sμ : μ {ω | observations (l' ++ [s, t]) ω = xs' ++ [i, j]} =
          μ {ω | observations (l' ++ [s]) ω = xs' ++ [i]} *
            ENNReal.ofReal (transition Q (↑(t - s) : ℝ) i j) :=
        hμt.step hμm.markov l' xs' s t i j ho' hl'
      have sν : ν {ω | observations (l' ++ [s, t]) ω = xs' ++ [i, j]} =
          ν {ω | observations (l' ++ [s]) ω = xs' ++ [i]} *
            ENNReal.ofReal (transition Q (↑(t - s) : ℝ) i j) :=
        hνt.step hνm.markov l' xs' s t i j ho' hl'
      rw [e1, e2, sμ, sν, ih hprefix (xs' ++ [i]) hl]

/-- A measure on paths is the path measure exactly when the coordinate process starts
from `p`, is a time-homogeneous Markov process, and has the transition probabilities
of `Q`. -/
theorem eq_pathMeasure_iff (hQ : IsGenerator Q) (d : ι) (p : PMF ι) (μ : Measure (Path ι)) :
    μ = pathMeasure Q d p ↔
      μ.map (coordinate 0) = p.toMeasure ∧ IsHomogeneousMarkovProcess coordinate μ ∧
        HasTransition Q coordinate μ := by
  constructor
  · rintro rfl
    exact ⟨pathMeasure_initial Q d p, pathMeasure_isHomogeneousMarkovProcess hQ d p,
      pathMeasure_hasTransition hQ d p⟩
  · rintro ⟨h0, hm, ht⟩
    have hprob : IsProbabilityMeasure μ := by
      refine ⟨?_⟩
      have h := congrArg (fun m : Measure ι => m Set.univ) h0
      simpa [Measure.map_apply (measurable_coordinate 0) MeasurableSet.univ] using h
    exact measure_ext_observations fun ts ho xs =>
      ht.observations_eq hm (pathMeasure_hasTransition hQ d p)
        (pathMeasure_isHomogeneousMarkovProcess hQ d p)
        (h0.trans (pathMeasure_initial Q d p).symm) ts ho xs

/-- For a generator `Q` and an initial distribution `p`, exactly one measure on paths
makes the coordinate process start from `p`, be a time-homogeneous Markov process, and
have the transition probabilities of `Q`. -/
theorem existsUnique_pathMeasure (hQ : IsGenerator Q) (p : PMF ι) :
    ∃! μ : Measure (Path ι),
      μ.map (coordinate 0) = p.toMeasure ∧ IsHomogeneousMarkovProcess coordinate μ ∧
        HasTransition Q coordinate μ := by
  obtain ⟨d, -⟩ := p.support_nonempty
  exact ⟨pathMeasure Q d p, (eq_pathMeasure_iff hQ d p _).1 rfl,
    fun μ h => (eq_pathMeasure_iff hQ d p μ).2 h⟩

/-- The path measure does not depend on the filler state. -/
theorem pathMeasure_filler (hQ : IsGenerator Q) (d d' : ι) (p : PMF ι) :
    pathMeasure Q d p = pathMeasure Q d' p :=
  (eq_pathMeasure_iff hQ d' p _).2 ((eq_pathMeasure_iff hQ d p _).1 rfl)

/-! ### The law of the chain, named without the construction -/

/-- The law on paths of the chain with generator `Q` that starts from `p`. It is defined
as the one measure of `existsUnique_pathMeasure`, so it mentions no filler state. -/
noncomputable def chainLaw (hQ : IsGenerator Q) (p : PMF ι) : Measure (Path ι) :=
  (existsUnique_pathMeasure hQ p).choose

/-- A measure on paths is the law of the chain exactly when the coordinate process
starts from `p`, is a time-homogeneous Markov process, and has the transition
probabilities of `Q`. -/
theorem eq_chainLaw_iff (hQ : IsGenerator Q) (p : PMF ι) (μ : Measure (Path ι)) :
    μ = chainLaw hQ p ↔
      μ.map (coordinate 0) = p.toMeasure ∧ IsHomogeneousMarkovProcess coordinate μ ∧
        HasTransition Q coordinate μ := by
  constructor
  · rintro rfl
    exact (existsUnique_pathMeasure hQ p).choose_spec.1
  · exact fun h => (existsUnique_pathMeasure hQ p).choose_spec.2 μ h

/-- The law of the chain is the constructed path measure, for any filler state. -/
theorem chainLaw_eq_pathMeasure (hQ : IsGenerator Q) (d : ι) (p : PMF ι) :
    chainLaw hQ p = pathMeasure Q d p :=
  (eq_pathMeasure_iff hQ d p _).2 ((eq_chainLaw_iff hQ p _).1 rfl)

instance chainLaw_isProbabilityMeasure (hQ : IsGenerator Q) (p : PMF ι) :
    IsProbabilityMeasure (chainLaw hQ p) := by
  obtain ⟨d, -⟩ := p.support_nonempty
  rw [chainLaw_eq_pathMeasure hQ d p]
  infer_instance

/-- Under the law of the chain the state at time `0` has the law `p`. -/
@[simp] theorem chainLaw_initial (hQ : IsGenerator Q) (p : PMF ι) :
    (chainLaw hQ p).map (coordinate 0) = p.toMeasure :=
  ((eq_chainLaw_iff hQ p _).1 rfl).1

/-- Under the law of the chain the coordinate process is a time-homogeneous Markov
process. -/
theorem chainLaw_isHomogeneousMarkovProcess (hQ : IsGenerator Q) (p : PMF ι) :
    IsHomogeneousMarkovProcess coordinate (chainLaw hQ p) :=
  ((eq_chainLaw_iff hQ p _).1 rfl).2.1

/-- Under the law of the chain the coordinate process has the transition probabilities
of `Q`. -/
theorem chainLaw_hasTransition (hQ : IsGenerator Q) (p : PMF ι) :
    HasTransition Q coordinate (chainLaw hQ p) :=
  ((eq_chainLaw_iff hQ p _).1 rfl).2.2

/-! ### The law of a process on any probability space -/

section

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {X : ℝ≥0 → Ω → ι}
  {P : Measure Ω} {X' : ℝ≥0 → Ω' → ι} {P' : Measure Ω'}

/-- A time-homogeneous Markov process that starts from `p` and has the transition
probabilities of the generator `Q` has the law of the chain as its law on paths. -/
theorem IsHomogeneousMarkovProcess.law_eq_chainLaw (hQ : IsGenerator Q) (p : PMF ι)
    (h : IsHomogeneousMarkovProcess X P) (ht : HasTransition Q X P)
    (h0 : P.map (X 0) = p.toMeasure) :
    P.map (fun ω u => X u ω) = chainLaw hQ p := by
  have hΦ : Measurable fun ω (u : ℝ≥0) => X u ω := Measurable.of_eval h.measurable
  refine (eq_chainLaw_iff hQ p _).2 ⟨?_, h.law, ht.law h.measurable⟩
  rw [Measure.map_map (measurable_coordinate 0) hΦ]
  exact h0

/-- Two time-homogeneous Markov processes with the transition probabilities of the same
matrix and the same law at time `0` have the same law on paths. They may live on
different probability spaces. -/
theorem IsHomogeneousMarkovProcess.law_eq [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : IsHomogeneousMarkovProcess X P) (ht : HasTransition Q X P)
    (h' : IsHomogeneousMarkovProcess X' P') (ht' : HasTransition Q X' P')
    (h0 : P.map (X 0) = P'.map (X' 0)) :
    P.map (fun ω u => X u ω) = P'.map (fun ω u => X' u ω) := by
  have hΦ : Measurable fun ω (u : ℝ≥0) => X u ω := Measurable.of_eval h.measurable
  have hΦ' : Measurable fun ω (u : ℝ≥0) => X' u ω := Measurable.of_eval h'.measurable
  refine measure_ext_observations fun ts ho xs =>
    (ht.law h.measurable).observations_eq h.law (ht'.law h'.measurable) h'.law ?_ ts ho xs
  rw [Measure.map_map (measurable_coordinate 0) hΦ,
    Measure.map_map (measurable_coordinate 0) hΦ']
  exact h0

end

end SympyProofs.FiniteMarkovChain
