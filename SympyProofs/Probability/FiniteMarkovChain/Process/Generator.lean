module

public import SympyProofs.Probability.FiniteMarkovChain.Process.Transition
public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Semigroup

/-!
# From the Markov property to the generator

This file starts from a time-homogeneous Markov process `X` on a probability space
`(Ω, P)`, with no matrix, and finds its generator.

Every such process has the transition probabilities of some generator. This is
`exists_generator_of_isHomogeneousMarkovProcess`. If every state is visited at some
time, the generator is unique, which is
`existsUnique_generator_of_isHomogeneousMarkovProcess`.

A state that is never visited leaves its row of the generator free, so that condition
cannot be dropped. The rows of the visited states are always determined, by
`HasTransition.generator_row_unique`.

The proof reads the transition probabilities of each state off the process at a time
when the state has positive probability, and uses "stay put" for a state that is never
visited. These form a semigroup of row-stochastic matrices that is continuous at time
`0`, so `existsUnique_generator_of_semigroup` applies.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

variable {ι Ω : Type*} [MeasurableSpace Ω]

section

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

private theorem sum_measure_inter_time {X : ℝ≥0 → Ω → ι} (hX : ∀ t, Measurable (X t))
    (P : Measure Ω) (A : Set Ω) (t : ℝ≥0) :
    ∑ j, P (A ∩ {ω | X t ω = j}) = P A := by
  have hm : ∀ j, MeasurableSet {ω | X t ω = j} := fun j =>
    hX t (measurableSet_singleton j)
  have h := sum_measure_preimage_singleton (μ := P.restrict A) Finset.univ
    (f := X t) (fun j _ => hm j)
  rw [Finset.coe_univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inter_comm]
  exact (Measure.restrict_apply (hm j)).symm

end

/-! ### Transition probabilities read off the process -/

variable [DecidableEq ι]

/-- The chance of being in `j` after a duration `t`, for a process in `i`. It is read
at a time when `i` has positive probability. A state that is never visited stays
put. -/
private noncomputable def moveProb (X : ℝ≥0 → Ω → ι) (P : Measure Ω) (t : ℝ≥0)
    (i j : ι) : ℝ≥0∞ :=
  if h : ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0 then
    P {ω | X h.choose ω = i ∧ X (h.choose + t) ω = j} / P {ω | X h.choose ω = i}
  else if i = j then 1 else 0

/-- The transition probabilities as a real matrix. -/
private noncomputable def moveMatrix (X : ℝ≥0 → Ω → ι) (P : Measure Ω) (t : ℝ≥0) :
    Matrix ι ι ℝ :=
  fun i j => (moveProb X P t i j).toReal

private theorem moveProb_of_not_visited {X : ℝ≥0 → Ω → ι} {P : Measure Ω} {i : ι}
    (hv : ¬ ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0) (t : ℝ≥0) (j : ι) :
    moveProb X P t i j = if i = j then 1 else 0 := by
  simp only [moveProb, hv, ↓reduceDIte]

section

variable [MeasurableSpace ι] {X : ℝ≥0 → Ω → ι} {P : Measure Ω} [IsProbabilityMeasure P]

private theorem measure_two_times (h : IsHomogeneousMarkovProcess X P)
    (s d : ℝ≥0) (i j : ι) :
    P {ω | X s ω = i ∧ X (s + d) ω = j} = P {ω | X s ω = i} * moveProb X P d i j := by
  by_cases hs : P {ω | X s ω = i} = 0
  · rw [measure_mono_null (fun ω hω => hω.1) hs, hs, zero_mul]
  · have hv : ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0 := ⟨s, hs⟩
    have e := h.homogeneous s hv.choose d i j
    simp only [moveProb, hv, ↓reduceDIte]
    rw [← mul_div_assoc, ENNReal.eq_div_iff hv.choose_spec (measure_ne_top P _),
      mul_comm, e, mul_comm]

private theorem measure_step (h : IsHomogeneousMarkovProcess X P)
    (F : Finset ℝ≥0) (x : ℝ≥0 → ι) (s t : ℝ≥0) (i j : ι) (hF : ∀ u ∈ F, u < s)
    (hst : s < t) :
    P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} =
      P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} * moveProb X P (t - s) i j := by
  have hm := h.markov F x s t i j hF hst
  have h2 := measure_two_times h s (t - s) i j
  rw [add_tsub_cancel_of_le hst.le] at h2
  rw [h2] at hm
  by_cases hm0 : P {ω | X s ω = i} = 0
  · have hA : P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i ∧ X t ω = j} = 0 :=
      measure_mono_null (fun ω hω => hω.2.1) hm0
    have hB : P {ω | (∀ u ∈ F, X u ω = x u) ∧ X s ω = i} = 0 :=
      measure_mono_null (fun ω hω => hω.2) hm0
    rw [hA, hB, zero_mul]
  · refine (ENNReal.mul_left_inj hm0 (measure_ne_top P _)).1 ?_
    rw [hm]
    ring

private theorem moveProb_zero (h : IsHomogeneousMarkovProcess X P) (i j : ι) :
    moveProb X P 0 i j = if i = j then 1 else 0 := by
  by_cases hv : ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0
  · obtain ⟨s, hs⟩ := hv
    refine (ENNReal.mul_right_inj hs (measure_ne_top P _)).1 ?_
    rw [← measure_two_times h s 0 i j]
    split_ifs with hij
    · subst hij
      simp
    · have e : {ω | X s ω = i ∧ X (s + 0) ω = j} = ∅ := by
        ext ω
        simp only [add_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        exact hij (h1.symm.trans h2)
      rw [e, measure_empty, mul_zero]
  · exact moveProb_of_not_visited hv 0 j

private theorem moveMatrix_zero (h : IsHomogeneousMarkovProcess X P) :
    moveMatrix X P 0 = 1 := by
  ext i j
  simp only [moveMatrix, moveProb_zero h, Matrix.one_apply]
  split_ifs <;> simp

private theorem tendsto_moveProb_diag (h : IsHomogeneousMarkovProcess X P) (i : ι) :
    Tendsto (fun t : ℝ≥0 => moveProb X P t i i) (𝓝 0) (𝓝 1) := by
  by_cases hv : ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0
  · obtain ⟨s, hs⟩ := hv
    have hq : ∀ t : ℝ≥0, moveProb X P t i i =
        P {ω | X s ω = i ∧ X (s + t) ω = i} / P {ω | X s ω = i} := fun t =>
      (ENNReal.eq_div_iff hs (measure_ne_top P _)).2 (measure_two_times h s t i i).symm
    simp_rw [hq]
    have hlim := ENNReal.Tendsto.div_const (b := P {ω | X s ω = i}) (h.continuous s i)
      (Or.inl hs)
    rwa [ENNReal.div_self hs (measure_ne_top P _)] at hlim
  · simp only [moveProb_of_not_visited hv, ↓reduceIte]
    exact tendsto_const_nhds

end

/-! ### The transition probabilities form a continuous stochastic semigroup -/

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

section

variable {X : ℝ≥0 → Ω → ι} {P : Measure Ω} [IsProbabilityMeasure P]

private theorem moveProb_sum (h : IsHomogeneousMarkovProcess X P) (t : ℝ≥0) (i : ι) :
    ∑ j, moveProb X P t i j = 1 := by
  by_cases hv : ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0
  · obtain ⟨s, hs⟩ := hv
    refine (ENNReal.mul_right_inj hs (measure_ne_top P _)).1 ?_
    rw [Finset.mul_sum, mul_one]
    simp_rw [← measure_two_times h s t i]
    exact sum_measure_inter_time h.measurable P {ω | X s ω = i} (s + t)
  · simp [moveProb_of_not_visited hv]

private theorem moveProb_ne_top (h : IsHomogeneousMarkovProcess X P) (t : ℝ≥0) (i j : ι) :
    moveProb X P t i j ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← moveProb_sum h t i]
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)

private theorem moveProb_add (h : IsHomogeneousMarkovProcess X P) (s t : ℝ≥0) (i k : ι) :
    moveProb X P (s + t) i k = ∑ j, moveProb X P s i j * moveProb X P t j k := by
  rcases eq_or_lt_of_le (zero_le (a := s)) with rfl | hs
  · simp [moveProb_zero h]
  rcases eq_or_lt_of_le (zero_le (a := t)) with rfl | ht
  · simp [moveProb_zero h]
  by_cases hv : ∃ r : ℝ≥0, P {ω | X r ω = i} ≠ 0
  · obtain ⟨r, hr⟩ := hv
    refine (ENNReal.mul_right_inj hr (measure_ne_top P _)).1 ?_
    rw [← measure_two_times h r (s + t) i k, Finset.mul_sum,
      ← sum_measure_inter_time h.measurable P {ω | X r ω = i ∧ X (r + (s + t)) ω = k} (r + s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : {ω | X r ω = i ∧ X (r + (s + t)) ω = k} ∩ {ω | X (r + s) ω = j} =
        {ω | (∀ u ∈ ({r} : Finset ℝ≥0), X u ω = i) ∧ X (r + s) ω = j ∧
          X (r + (s + t)) ω = k} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
      tauto
    have e2 : {ω | (∀ u ∈ ({r} : Finset ℝ≥0), X u ω = i) ∧ X (r + s) ω = j} =
        {ω | X r ω = i ∧ X (r + s) ω = j} := by
      ext ω
      simp
    have hF : ∀ u ∈ ({r} : Finset ℝ≥0), u < r + s := fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact lt_add_of_pos_right r hs
    have hst : r + s < r + (s + t) := by
      rw [← add_assoc]
      exact lt_add_of_pos_right _ ht
    have hd : r + (s + t) - (r + s) = t := by
      rw [← add_assoc, add_tsub_cancel_left]
    rw [e1, measure_step h {r} (fun _ => i) (r + s) (r + (s + t)) j k hF hst, e2, hd,
      measure_two_times h r s i j, mul_assoc]
  · simp [moveProb_of_not_visited hv]

private theorem moveMatrix_mem_rowStochastic (h : IsHomogeneousMarkovProcess X P) (t : ℝ≥0) :
    moveMatrix X P t ∈ Matrix.rowStochastic ℝ ι := by
  refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun i j => ENNReal.toReal_nonneg, fun i => ?_⟩
  simp only [moveMatrix]
  rw [← ENNReal.toReal_sum fun j _ => moveProb_ne_top h t i j, moveProb_sum h t i,
    ENNReal.toReal_one]

private theorem moveMatrix_add (h : IsHomogeneousMarkovProcess X P) (s t : ℝ≥0) :
    moveMatrix X P (s + t) = moveMatrix X P s * moveMatrix X P t := by
  ext i k
  simp only [moveMatrix, Matrix.mul_apply, moveProb_add h]
  rw [ENNReal.toReal_sum fun j _ =>
    ENNReal.mul_ne_top (moveProb_ne_top h s i j) (moveProb_ne_top h t j k)]
  simp [ENNReal.toReal_mul]

private theorem continuousAt_moveMatrix (h : IsHomogeneousMarkovProcess X P) :
    ContinuousAt (moveMatrix X P) 0 := by
  rw [ContinuousAt, moveMatrix_zero h]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hdiag : Tendsto (fun t : ℝ≥0 => moveMatrix X P t i i) (𝓝 0) (𝓝 1) := by
    have hr : Tendsto (fun t : ℝ≥0 => (moveProb X P t i i).toReal) (𝓝 0)
        (𝓝 (1 : ℝ≥0∞).toReal) :=
      (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (tendsto_moveProb_diag h i)
    rw [ENNReal.toReal_one] at hr
    exact hr
  by_cases hij : i = j
  · subst hij
    simpa using hdiag
  · have hlim : Tendsto (fun t : ℝ≥0 => 1 - moveMatrix X P t i i) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiag
    have hle : ∀ t : ℝ≥0, moveMatrix X P t i j ≤ 1 - moveMatrix X P t i i := by
      intro t
      have hst := moveMatrix_mem_rowStochastic h t
      have hsum := (Matrix.mem_rowStochastic_iff_sum.1 hst).2 i
      have hnn := (Matrix.mem_rowStochastic_iff_sum.1 hst).1 i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hj : moveMatrix X P t i j ≤ ∑ k ∈ Finset.univ.erase i, moveMatrix X P t i k :=
        Finset.single_le_sum (fun k _ => hnn k) (by simp [Ne.symm hij])
      linarith
    have h0 : (1 : Matrix ι ι ℝ) i j = 0 := Matrix.one_apply_ne hij
    rw [h0]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun t => ENNReal.toReal_nonneg) hle

end

/-! ### Existence and uniqueness of the generator -/

/-- A time-homogeneous Markov process has the transition probabilities of some
generator. -/
theorem exists_generator_of_isHomogeneousMarkovProcess {X : ℝ≥0 → Ω → ι}
    {P : Measure Ω} [IsProbabilityMeasure P] (h : IsHomogeneousMarkovProcess X P) :
    ∃ Q : Matrix ι ι ℝ, IsGenerator Q ∧ HasTransition Q X P := by
  obtain ⟨Q, ⟨hQ, hPQ⟩, -⟩ := existsUnique_generator_of_semigroup (moveMatrix X P)
    (moveMatrix_mem_rowStochastic h) (moveMatrix_zero h) (moveMatrix_add h)
    (continuousAt_moveMatrix h)
  refine ⟨Q, hQ, fun s t i j => ?_⟩
  rw [measure_two_times h s t i j, ← hPQ t]
  simp only [moveMatrix]
  rw [ENNReal.ofReal_toReal (moveProb_ne_top h t i j)]

/-- A time-homogeneous Markov process that visits every state at some time has the
transition probabilities of exactly one generator. -/
theorem existsUnique_generator_of_isHomogeneousMarkovProcess {X : ℝ≥0 → Ω → ι}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hvis : ∀ i, ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0) (h : IsHomogeneousMarkovProcess X P) :
    ∃! Q : Matrix ι ι ℝ, IsGenerator Q ∧ HasTransition Q X P := by
  obtain ⟨Q, hQ, hT⟩ := exists_generator_of_isHomogeneousMarkovProcess h
  exact ⟨Q, ⟨hQ, hT⟩, fun Q' hQ' => hQ'.2.generator_unique hQ'.1 hQ hvis hT⟩

end SympyProofs.FiniteMarkovChain
