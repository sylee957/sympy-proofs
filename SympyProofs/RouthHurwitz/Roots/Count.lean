import Mathlib

/-!
# Half-plane root counts along polynomial deformations

Counts use `Polynomial.roots`, hence include multiplicities. The continuity
argument uses compact spaces of finite root factorizations, not a choice of
individually continuous roots.
-/

namespace Polynomial
open scoped BigOperators NNReal
open Set
attribute [local instance] Classical.propDecidable

/-- Roots in a region, counted with multiplicity. -/
noncomputable def regionCount (p : ℂ[X]) (P : ℂ → Prop) : ℕ := by
  classical
  exact (p.roots.filter P).card

/-- Roots in the open right half-plane, counted with multiplicity. -/
noncomputable def rightCount (p : ℂ[X]) : ℕ := regionCount p (fun z => 0 < z.re)

/-- Roots on the imaginary axis, counted with multiplicity. -/
noncomputable def axisCount (p : ℂ[X]) : ℕ := regionCount p (fun z => z.re = 0)

private theorem regionCount_prod (P : ℂ → Prop) (r : ι → ℂ) (s : Finset ι) :
    regionCount (∏ i ∈ s, (X - C (r i))) P = ∑ i ∈ s, if P (r i) then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [regionCount]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hn : (X - C (r i)) * ∏ j ∈ s, (X - C (r j)) ≠ 0 := by
        apply mul_ne_zero (X_sub_C_ne_zero _)
        exact Finset.prod_ne_zero_iff.mpr (fun j _ => X_sub_C_ne_zero _)
      simp only [regionCount, roots_mul hn, Multiset.filter_add, Multiset.card_add,
        roots_X_sub_C]
      change (({r i} : Multiset ℂ).filter P).card +
        regionCount (∏ j ∈ s, (X - C (r j))) P = _
      rw [ih]
      by_cases h : P (r i) <;> simp only [Multiset.filter_singleton, h, if_true, if_false, Multiset.card_singleton, Multiset.empty_eq_zero, Multiset.card_zero]

private theorem regionCount_factorization (P : ℂ → Prop) (n : ℕ) (r : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    regionCount (C c * ∏ i, (X - C (r i))) P =
      (Finset.univ.filter (fun i => P (r i))).card := by
  classical
  unfold regionCount
  rw [roots_C_mul _ hc]
  change regionCount (∏ i, (X - C (r i))) P = _
  rw [regionCount_prod]
  simp

private theorem rightCount_factorization (n : ℕ) (r : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    rightCount (C c * ∏ i, (X - C (r i))) =
      (Finset.univ.filter (fun i => 0 < (r i).re)).card :=
  regionCount_factorization _ n r c hc

private theorem exists_root_tuple (p : ℂ[X]) (n : ℕ) (hd : p.natDegree = n) :
    ∃ r : Fin n → ℂ, p = C p.leadingCoeff * ∏ i, (X - C (r i)) := by
  have he : ∃ (m : ℕ) (r : Fin m → ℂ), (List.ofFn r : Multiset ℂ) = p.roots := by
    refine ⟨p.roots.toList.length, p.roots.toList.get, ?_⟩
    exact (congrArg (fun l : List ℂ => (l : Multiset ℂ)) (List.ofFn_get p.roots.toList)).trans
      (Multiset.coe_toList p.roots)
  obtain ⟨m, r, hr⟩ := he
  have hm : m = n := by
    have := congrArg Multiset.card hr
    simpa [← (IsAlgClosed.splits p).natDegree_eq_card_roots, hd] using this
  subst m
  refine ⟨r, ?_⟩
  calc
    p = C p.leadingCoeff * (p.roots.map (fun z => X - C z)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = _ := by rw [← hr]; simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

private theorem root_tuple_isRoot (n : ℕ) (r : Fin n → ℂ) (c : ℂ) (i : Fin n) :
    (C c * ∏ j, (X - C (r j))).IsRoot (r i) := by
  simp only [IsRoot, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have h : ∏ j, (r i - r j) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  rw [h, mul_zero]

private theorem factorization_continuous (n : ℕ) (z : ℂ) :
    Continuous (fun r : Fin n → ℂ => ∏ i, (z - r i)) := by fun_prop

/-- A uniform root bound on a compact family of fixed-degree nonzero
polynomials. Continuity is stated coefficientwise. -/
theorem exists_uniform_root_bound {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (p : T → ℂ[X]) (n : ℕ) (hp : ∀ t, p t ≠ 0) (hd : ∀ t, (p t).natDegree = n)
    (hc : ∀ i, Continuous (fun t => (p t).coeff i)) :
    ∃ M : ℝ, ∀ t z, (p t).IsRoot z → ‖z‖ ≤ M := by
  let b : T → ℝ := fun t => (∑ i ∈ Finset.range n, ‖(p t).coeff i‖) / ‖(p t).coeff n‖ + 1
  have hb : Continuous b := by
    apply Continuous.add _ continuous_const
    apply Continuous.div
    · exact continuous_finsetSum _ (fun i _ => (hc i).norm)
    · exact (hc n).norm
    · intro t
      rw [← hd t, coeff_natDegree]
      exact norm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr (hp t))
  obtain ⟨M, hM⟩ := (isCompact_range hb).bddAbove
  refine ⟨M, fun t z hz => le_trans ?_ (hM ⟨t, rfl⟩)⟩
  have hh := hz.norm_lt_cauchyBound (hp t)
  have hsup : (Finset.range n).sup (fun i => ‖(p t).coeff i‖₊) ≤
      ∑ i ∈ Finset.range n, ‖(p t).coeff i‖₊ := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (fun j _ => show (0 : ℝ≥0) ≤ ‖(p t).coeff j‖₊ from bot_le) hi
  have hh' : ‖z‖ ≤ (((Finset.range n).sup (fun i => ‖(p t).coeff i‖₊) : ℝ≥0) : ℝ) /
      ‖(p t).coeff n‖ + 1 := by
    exact_mod_cast (show ‖z‖₊ ≤ (Finset.range n).sup (fun i => ‖(p t).coeff i‖₊) /
      ‖(p t).coeff n‖₊ + 1 by simpa [cauchyBound, hd, leadingCoeff] using hh.le)
  apply hh'.trans
  dsimp [b]
  gcongr
  simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr hsup)

/-- On a compact family of fixed-degree polynomials with a constant
imaginary-axis root count, the right-half-plane root count is continuous
into the discrete natural numbers. All counts include multiplicities. -/
theorem continuous_rightCount_of_axisCount {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] (p : T → ℂ[X]) (n m : ℕ)
    (hp : ∀ t, p t ≠ 0) (hd : ∀ t, (p t).natDegree = n)
    (hc : ∀ i, Continuous (fun t => (p t).coeff i))
    (haxis : ∀ t, axisCount (p t) = m) :
    Continuous (fun t => rightCount (p t)) := by
  classical
  obtain ⟨M, hM⟩ := exists_uniform_root_bound p n hp hd hc
  have heval (z : ℂ) : Continuous (fun t => (p t).eval z) := by
    have he : (fun t => (p t).eval z) =
        (fun t => ∑ i ∈ Finset.range (n + 1), (p t).coeff i * z ^ i) := by
      funext t; rw [eval_eq_sum_range, hd]
    rw [he]
    exact continuous_finsetSum _ (fun i _ => (hc i).mul continuous_const)
  have hlc : Continuous (fun t => (p t).leadingCoeff) := by
    simpa only [leadingCoeff, hd] using hc n
  let B : Set (Fin n → ℂ) := {r | ∀ i, ‖r i‖ ≤ M}
  have hB : IsCompact B := by
    simpa only [B, Metric.mem_closedBall, dist_zero_right] using
      isCompact_pi_infinite (fun _ : Fin n => isCompact_closedBall (0 : ℂ) M)
  let K : Finset (Fin n) → Finset (Fin n) → Set (T × (Fin n → ℂ)) := fun S J =>
    (Set.univ ×ˢ B) ∩ {v |
      (∀ z, (p v.1).eval z = (p v.1).leadingCoeff * ∏ i, (z - v.2 i)) ∧
      (∀ i, if i ∈ J then (v.2 i).re = 0
        else if i ∈ S then 0 ≤ (v.2 i).re else (v.2 i).re ≤ 0)}
  have hK (S J : Finset (Fin n)) : IsCompact (K S J) := by
    apply (isCompact_univ.prod hB).inter_right
    simp only [Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro z
      apply isClosed_eq ((heval z).comp continuous_fst)
      exact (hlc.comp continuous_fst).mul ((factorization_continuous n z).comp continuous_snd)
    · apply isClosed_iInter
      intro i
      by_cases hi : i ∈ J
      · simp only [if_pos hi]
        exact isClosed_eq (by fun_prop) continuous_const
      · simp only [if_neg hi]
        by_cases hi : i ∈ S
        · simp only [if_pos hi]
          exact isClosed_le continuous_const (by fun_prop)
        · simp only [if_neg hi]
          exact isClosed_le (by fun_prop) continuous_const
  have hfactors {t : T} {r : Fin n → ℂ}
      (he : ∀ z, (p t).eval z = (p t).leadingCoeff * ∏ i, (z - r i)) :
      p t = C (p t).leadingCoeff * ∏ i, (X - C (r i)) := by
    apply Polynomial.funext
    intro z
    simpa [eval_prod] using he z
  have hcount {S J : Finset (Fin n)} {t : T} {r : Fin n → ℂ}
      (hJ : J.card = m) (hdisj : Disjoint S J)
      (he : ∀ z, (p t).eval z = (p t).leadingCoeff * ∏ i, (z - r i))
      (hs : ∀ i, if i ∈ J then (r i).re = 0
        else if i ∈ S then 0 ≤ (r i).re else (r i).re ≤ 0) :
      rightCount (p t) = S.card := by
    have hfac := hfactors he
    let Z := Finset.univ.filter (fun i => (r i).re = 0)
    have hZ : Z.card = m := by
      have hh := regionCount_factorization (fun z => z.re = 0) n r _ (leadingCoeff_ne_zero.mpr (hp t))
      rw [← hfac] at hh
      exact hh.symm.trans (haxis t)
    have hsub : J ⊆ Z := by
      intro i hi
      have hh := hs i
      simp only [if_pos hi] at hh
      simp [Z, hh]
    have hJZ : J = Z := Finset.eq_of_subset_of_card_le hsub (by omega)
    have heq : Finset.univ.filter (fun i => 0 < (r i).re) = S := by
      ext i
      have hh := hs i
      by_cases hj : i ∈ J
      · simp only [if_pos hj] at hh
        have hn : i ∉ S := fun hi => Finset.disjoint_left.mp hdisj hi hj
        simp [hh, hn]
      · have hn : (r i).re ≠ 0 := by
          intro hz
          apply hj
          rw [hJZ]
          simp [Z, hz]
        simp only [if_neg hj] at hh
        by_cases hi : i ∈ S
        · simp only [if_pos hi] at hh
          simp [hi, lt_of_le_of_ne hh (Ne.symm hn)]
        · simp only [if_neg hi] at hh
          simp [hi, not_lt.mpr hh]
    rw [hfac, rightCount_factorization n r _ (leadingCoeff_ne_zero.mpr (hp t)), heq]
  apply continuous_iff_isClosed.mpr
  intro A _
  have heq : (fun t => rightCount (p t)) ⁻¹' A =
      ⋃ SJ : Finset (Fin n) × Finset (Fin n),
        if SJ.2.card = m ∧ Disjoint SJ.1 SJ.2 ∧ SJ.1.card ∈ A then
          Prod.fst '' K SJ.1 SJ.2 else ∅ := by
    ext t
    constructor
    · intro ht
      obtain ⟨r, hr⟩ := exists_root_tuple (p t) n (hd t)
      let S := Finset.univ.filter (fun i => 0 < (r i).re)
      let J := Finset.univ.filter (fun i => (r i).re = 0)
      have hS : S.card ∈ A := by
        have hh := rightCount_factorization n r _ (leadingCoeff_ne_zero.mpr (hp t))
        rw [← hr] at hh
        exact hh ▸ ht
      have hJ : J.card = m := by
        have hh := regionCount_factorization (fun z => z.re = 0) n r _ (leadingCoeff_ne_zero.mpr (hp t))
        rw [← hr] at hh
        exact hh.symm.trans (haxis t)
      have hdisj : Disjoint S J := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        have hpos : 0 < (r i).re := (Finset.mem_filter.mp hi).2
        have hz : (r i).re = 0 := (Finset.mem_filter.mp hj).2
        linarith
      apply Set.mem_iUnion.mpr
      refine ⟨(S, J), ?_⟩
      rw [if_pos ⟨hJ, hdisj, hS⟩]
      refine ⟨(t, r), ?_, rfl⟩
      refine ⟨⟨Set.mem_univ _, fun i => ?_⟩, ?_, ?_⟩
      · exact hM t (r i) (hr ▸ root_tuple_isRoot n r (p t).leadingCoeff i)
      · intro z
        simpa [eval_prod] using congrArg (Polynomial.eval z) hr
      · intro i
        by_cases hj : (r i).re = 0
        · simp [J, hj]
        · by_cases hi : 0 < (r i).re
          · simp [S, J, hj, hi, hi.le]
          · simp [S, J, hj, hi, le_of_not_gt hi]
    · intro ht
      obtain ⟨⟨S, J⟩, hS⟩ := Set.mem_iUnion.mp ht
      split_ifs at hS with hSA
      · obtain ⟨⟨t', r⟩, hKmem, heq⟩ := hS
        have htt : t' = t := heq
        subst t'
        change rightCount (p t) ∈ A
        rw [hcount hSA.1 hSA.2.1 hKmem.2.1 hKmem.2.2]
        exact hSA.2.2
      · exact False.elim (Set.notMem_empty _ hS)
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro SJ
  split_ifs
  · exact ((hK SJ.1 SJ.2).image continuous_fst).isClosed
  · exact isClosed_empty

/-- Full root-count invariance on connected compact parameter spaces when
degree and total imaginary-axis multiplicity stay constant. -/
theorem rightCount_eq_of_connected_axisCount {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [PreconnectedSpace T]
    (p : T → ℂ[X]) (n m : ℕ) (hp : ∀ t, p t ≠ 0) (hd : ∀ t, (p t).natDegree = n)
    (hc : ∀ i, Continuous (fun t => (p t).coeff i))
    (haxis : ∀ t, axisCount (p t) = m) (s t : T) :
    rightCount (p s) = rightCount (p t) :=
  PreconnectedSpace.constant inferInstance (continuous_rightCount_of_axisCount p n m hp hd hc haxis)

/-- Pointwise equality of imaginary-axis multiplicities gives equality of
the total imaginary-axis counts, including repeated roots. -/
theorem axisCount_eq_of_rootMultiplicity (p q : ℂ[X])
    (h : ∀ z, z.re = 0 → p.rootMultiplicity z = q.rootMultiplicity z) :
    axisCount p = axisCount q := by
  classical
  unfold axisCount regionCount
  congr 1
  apply Multiset.ext.mpr
  intro z
  by_cases hz : z.re = 0
  · simp only [Multiset.count_filter, if_pos hz, count_roots, h z hz]
  · simp only [Multiset.count_filter, if_neg hz]

/-- A polynomial-valued affine path with fixed degree and fixed boundary
multiplicities has equal right-half-plane counts at its endpoints. -/
theorem rightCount_affine (A B : ℂ[X]) (n : ℕ)
    (hp : ∀ t : unitInterval, A + C (t : ℂ) * B ≠ 0)
    (hd : ∀ t : unitInterval, (A + C (t : ℂ) * B).natDegree = n)
    (haxis : ∀ (t : unitInterval) z, z.re = 0 →
      (A + C (t : ℂ) * B).rootMultiplicity z = A.rootMultiplicity z) :
    rightCount (A + B) = rightCount A := by
  have hc (i : ℕ) : Continuous (fun t : unitInterval => (A + C (t : ℂ) * B).coeff i) := by
    simp only [coeff_add, coeff_C_mul]
    fun_prop
  have hm (t : unitInterval) : axisCount (A + C (t : ℂ) * B) = axisCount A :=
    axisCount_eq_of_rootMultiplicity _ _ (haxis t)
  have h := rightCount_eq_of_connected_axisCount
    (fun t : unitInterval => A + C (t : ℂ) * B) n (axisCount A) hp hd hc hm 1 0
  simpa using h

/-- A lower-degree affine perturbation cannot change the degree. -/
theorem natDegree_affine_of_lt (A B : ℂ[X]) (h : B.natDegree < A.natDegree) (t : ℂ) :
    (A + C t * B).natDegree = A.natDegree :=
  natDegree_add_eq_left_of_natDegree_lt ((natDegree_C_mul_le _ _).trans_lt h)

/-- A limit principle for root counts. A convergent sequence of fixed-degree
polynomials can be counted by classifying the half-plane approached by each
limiting root. The classification premise concerns individual root sequences,
not a count or a choice of continuous root labels. -/
theorem regionCount_of_root_limits (p : ℕ → ℂ[X]) (q : ℂ[X]) (n c : ℕ)
    (P : ℂ → Prop) (hp : ∀ k, p k ≠ 0) (hq : q ≠ 0)
    (hd : ∀ k, (p k).natDegree = n) (hqd : q.natDegree = n)
    (hc : ∀ i, Filter.Tendsto (fun k => (p k).coeff i) Filter.atTop (nhds (q.coeff i)))
    (M : ℝ) (hbound : ∀ k z, (p k).IsRoot z → ‖z‖ ≤ M)
    (hcount : ∀ k, rightCount (p k) = c)
    (hlimits : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (r : ℕ → ℂ) z,
      q.IsRoot z → (∀ k, (p (φ k)).IsRoot (r k)) →
      Filter.Tendsto r Filter.atTop (nhds z) →
      ∀ᶠ k in Filter.atTop, (0 < (r k).re ↔ P z)) : c = regionCount q P := by
  classical
  choose r hr using fun k => exists_root_tuple (p k) n (hd k)
  let B : Set (Fin n → ℂ) := {r | ∀ i, ‖r i‖ ≤ M}
  have hB : IsCompact B := by
    simpa only [B, Metric.mem_closedBall, dist_zero_right] using
      isCompact_pi_infinite (fun _ : Fin n => isCompact_closedBall (0 : ℂ) M)
  have hrB (k : ℕ) : r k ∈ B := fun i =>
    hbound k (r k i) (hr k ▸ root_tuple_isRoot n (r k) (p k).leadingCoeff i)
  obtain ⟨r₀, _, φ, hφ, hconv⟩ := hB.tendsto_subseq hrB
  have hcoord (i : Fin n) : Filter.Tendsto (fun k => r (φ k) i) Filter.atTop (nhds (r₀ i)) :=
    tendsto_pi_nhds.mp hconv i
  have heval (z : ℂ) : Filter.Tendsto (fun k => (p k).eval z) Filter.atTop (nhds (q.eval z)) := by
    have hpE (k : ℕ) : (p k).eval z = ∑ i ∈ Finset.range (n + 1), (p k).coeff i * z ^ i := by
      rw [eval_eq_sum_range, hd]
    have hqE : q.eval z = ∑ i ∈ Finset.range (n + 1), q.coeff i * z ^ i := by
      rw [eval_eq_sum_range, hqd]
    simp only [hpE, hqE]
    exact tendsto_finsetSum _ (fun i _ => (hc i).mul_const _)
  have hlc : Filter.Tendsto (fun k => (p (φ k)).leadingCoeff) Filter.atTop (nhds q.leadingCoeff) := by
    simp only [leadingCoeff, hd, hqd]
    exact (hc n).comp hφ.tendsto_atTop
  have hfac : q = C q.leadingCoeff * ∏ i, (X - C (r₀ i)) := by
    apply Polynomial.funext
    intro z
    have hh := hlc.mul ((factorization_continuous n z).tendsto r₀ |>.comp hconv)
    have hpeq : (fun k => (p (φ k)).eval z) =
        (fun k => (p (φ k)).leadingCoeff * ∏ i, (z - r (φ k) i)) := by
      funext k
      simpa [eval_prod] using congrArg (Polynomial.eval z) (hr (φ k))
    have hl := (heval z).comp hφ.tendsto_atTop
    change Filter.Tendsto (fun k => (p (φ k)).eval z) _ _ at hl
    rw [hpeq] at hl
    simpa [eval_prod] using tendsto_nhds_unique hl hh
  have hsign : ∀ᶠ k in Filter.atTop, ∀ i : Fin n, (0 < (r (φ k) i).re ↔ P (r₀ i)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply hlimits φ hφ (fun k => r (φ k) i) (r₀ i)
    · exact hfac ▸ root_tuple_isRoot n r₀ q.leadingCoeff i
    · intro k
      exact hr (φ k) ▸ root_tuple_isRoot n (r (φ k)) (p (φ k)).leadingCoeff i
    · exact hcoord i
  obtain ⟨k, hk⟩ := hsign.exists
  have hsame : Finset.univ.filter (fun i => 0 < (r (φ k) i).re) =
      Finset.univ.filter (fun i => P (r₀ i)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk i]
  calc
    c = rightCount (p (φ k)) := (hcount _).symm
    _ = (Finset.univ.filter (fun i => 0 < (r (φ k) i).re)).card := by
      conv_lhs => rw [hr (φ k)]
      exact rightCount_factorization n (r (φ k)) _ (leadingCoeff_ne_zero.mpr (hp _))
    _ = (Finset.univ.filter (fun i => P (r₀ i))).card := congrArg Finset.card hsame
    _ = regionCount q P := by
      conv_rhs => rw [hfac]
      exact (regionCount_factorization P n r₀ _ (leadingCoeff_ne_zero.mpr hq)).symm

set_option maxHeartbeats 800000 in
/-- Roots approaching an imaginary-axis root under a positive derivative
perturbation cannot approach it from the open right half-plane. Multiplicity
is arbitrary: repeated roots may remain on the axis. -/
theorem derivative_perturbation_eventually_nonpositive (p : ℂ[X]) (hp : p ≠ 0)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (htlim : Filter.Tendsto t Filter.atTop (nhds 0)) (r : ℕ → ℂ) (z : ℂ)
    (hz : z.re = 0) (hr : p.IsRoot z)
    (hroot : ∀ k, (p + C (t k : ℂ) * p.derivative).IsRoot (r k))
    (hrlim : Filter.Tendsto r Filter.atTop (nhds z)) :
    ∀ᶠ k in Filter.atTop, (r k).re ≤ 0 := by
  have hmpos : 0 < p.rootMultiplicity z := (rootMultiplicity_pos hp).mpr hr
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let g := p /ₘ (X - C z) ^ p.rootMultiplicity z
  have hg : g.eval z ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  have hfac : p = (X - C z) ^ (m + 1) * g := by
    change p = (X - C z) ^ m.succ * g
    rw [← hm]
    exact (pow_mul_divByMonic_rootMultiplicity_eq p z).symm
  have hG := g.continuous.tendsto z |>.comp hrlim
  have hD := g.derivative.continuous.tendsto z |>.comp hrlim
  have hT : Filter.Tendsto (fun k => (t k : ℂ)) Filter.atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp htlim
  let b (k : ℕ) := 1 + (t k : ℂ) * g.derivative.eval (r k) / g.eval (r k)
  have hb : Filter.Tendsto b Filter.atTop (nhds 1) := by
    simpa [b] using Filter.Tendsto.const_add 1 ((hT.mul hD).div hG hg)
  have hbre : ∀ᶠ k in Filter.atTop, 0 < (b k).re :=
    (Complex.continuous_re.tendsto 1 |>.comp hb).eventually_const_lt (by simp)
  have hgE : ∀ᶠ k in Filter.atTop, g.eval (r k) ≠ 0 := hG.eventually_ne hg
  filter_upwards [hbre, hgE] with k hbk hgk
  by_cases he : r k = z
  · simp [he, hz]
  have hfact : (p + C (t k : ℂ) * p.derivative).eval (r k) =
      (r k - z) ^ m * ((r k - z) * (g.eval (r k) + (t k : ℂ) * g.derivative.eval (r k)) +
        (t k : ℂ) * (m + 1) * g.eval (r k)) := by
    conv_lhs => rw [hfac]
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C,
      sub_zero, Nat.add_sub_cancel, mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
    push_cast
    ring
  have heq := hroot k
  rw [IsRoot, hfact] at heq
  have hinner := (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr he))
  have hnormalized : (r k - z) * b k = -(t k : ℂ) * (m + 1) := by
    dsimp [b]
    field_simp
    linear_combination hinner
  have hbne : b k ≠ 0 := by intro h; simp [h] at hbk
  have heval : r k - z = (-(t k : ℂ) * (m + 1)) / b k :=
    (eq_div_iff hbne).mpr hnormalized
  have hreal := congrArg Complex.re heval
  simp only [Complex.sub_re, hz, sub_zero, Complex.div_re, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.add_im, Complex.natCast_im,
    Complex.one_im, mul_zero, sub_zero, zero_mul, Complex.mul_im, add_zero,
    zero_div] at hreal
  rw [hreal]
  exact le_of_lt (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (ht k)) (by positivity)) hbk) (Complex.normSq_pos.mpr hbne))

/-- Derivative perturbations preserve the right-half-plane count when their
positive-parameter imaginary-axis counts are constant. The limiting endpoint
is justified even when the original polynomial has repeated boundary roots. -/
theorem rightCount_add_derivative (p : ℂ[X]) (hn : p.natDegree ≠ 0)
    (haxis : ∀ t : ℝ, 0 < t → t ≤ 1 →
      axisCount (p + C (t : ℂ) * p.derivative) = axisCount (p + p.derivative)) :
    rightCount (p + p.derivative) = rightCount p := by
  have hd (t : ℝ) : (p + C (t : ℂ) * p.derivative).natDegree = p.natDegree :=
    natDegree_affine_of_lt _ _ (natDegree_derivative_lt hn) _
  have hp (t : ℝ) : p + C (t : ℂ) * p.derivative ≠ 0 := by
    intro h
    have hh := hd t
    rw [h, natDegree_zero] at hh
    exact hn hh.symm
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have hcount (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      rightCount (p + C (t : ℂ) * p.derivative) = rightCount (p + p.derivative) := by
    let a (x : unitInterval) : ℝ := t + (1 - t) * x
    have ha (x : unitInterval) : 0 < a x ∧ a x ≤ 1 := by
      have hx0 := x.property.1
      have hx1 := x.property.2
      dsimp [a]
      constructor <;> nlinarith
    have hc (i : ℕ) : Continuous (fun x : unitInterval =>
        (p + C (a x : ℂ) * p.derivative).coeff i) := by
      simp only [coeff_add, coeff_C_mul]
      dsimp [a]
      fun_prop
    have hh := rightCount_eq_of_connected_axisCount
      (fun x : unitInterval => p + C (a x : ℂ) * p.derivative)
      p.natDegree (axisCount (p + p.derivative))
      (fun x => hp (a x)) (fun x => hd (a x)) hc
      (fun x => haxis (a x) (ha x).1 (ha x).2) 0 1
    simpa [a] using hh
  let e (k : ℕ) : ℝ := 1 / (k + 1)
  have hepos (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have hele (k : ℕ) : e k ≤ 1 := by
    dsimp [e]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have helim : Filter.Tendsto e Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcoeff (i : ℕ) : Continuous (fun t : unitInterval =>
      (p + C (t : ℂ) * p.derivative).coeff i) := by
    simp only [coeff_add, coeff_C_mul]
    fun_prop
  obtain ⟨M, hM⟩ := exists_uniform_root_bound
    (fun t : unitInterval => p + C (t : ℂ) * p.derivative) p.natDegree
    (fun t => hp t) (fun t => hd t) hcoeff
  refine regionCount_of_root_limits (fun k => p + C (e k : ℂ) * p.derivative)
    p p.natDegree (rightCount (p + p.derivative)) (fun z => 0 < z.re)
    (fun k => hp (e k)) hp0 (fun k => hd (e k)) rfl ?_ M ?_ ?_ ?_
  · intro i
    simp only [coeff_add, coeff_C_mul]
    have heC : Filter.Tendsto (fun k => (e k : ℂ)) Filter.atTop (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp helim
    simpa using (heC.mul_const (p.derivative.coeff i)).const_add (p.coeff i)
  · intro k z hz
    exact hM ⟨e k, (hepos k).le, hele k⟩ z hz
  · intro k
    exact hcount (e k) (hepos k) (hele k)
  · intro φ hφ r z hz hroot hlim
    have hreal : Filter.Tendsto (fun k => (r k).re) Filter.atTop (nhds z.re) :=
      Complex.continuous_re.continuousAt.tendsto.comp hlim
    rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
    · filter_upwards [hreal.eventually_lt_const hneg] with k hk
      simp [not_lt.mpr hk.le, not_lt.mpr hneg.le]
    · have hh := derivative_perturbation_eventually_nonpositive p hp0
        (fun k => e (φ k)) (fun k => hepos (φ k))
        (helim.comp hφ.tendsto_atTop) r z hzero hz hroot hlim
      filter_upwards [hh] with k hk
      simp [not_lt.mpr hk, hzero]
    · filter_upwards [hreal.eventually_const_lt hpos] with k hk
      simp [hk, hpos]

end Polynomial
