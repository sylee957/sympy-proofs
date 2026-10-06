import SympyProofs.RouthHurwitz.Table.RootCount

/-! Mathematical invariants of a current row pair, independent of any recursive table. -/
namespace RouthHurwitz
open Polynomial
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

/-- Every root lies in the open left half-plane. -/
def HurwitzStable (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.re < 0

def ComplexStable (p : ℂ[X]) : Prop := ∀ z, p.IsRoot z → z.re < 0

private theorem regionCount_zero_iff (p : ℂ[X]) (hp : p ≠ 0) (W : ℂ → Prop) :
    regionCount p W = 0 ↔ ∀ z, p.IsRoot z → ¬ W z := by
  classical
  simp only [regionCount, Multiset.card_eq_zero, Multiset.filter_eq_nil, mem_roots hp]

theorem complexStable_iff_counts (p : ℂ[X]) (hp : p ≠ 0) :
    ComplexStable p ↔ rightCount p = 0 ∧ axisCount p = 0 := by
  rw [rightCount, axisCount, regionCount_zero_iff p hp, regionCount_zero_iff p hp]
  constructor
  · intro h
    exact ⟨fun z hz => not_lt.mpr (h z hz).le, fun z hz => ne_of_lt (h z hz)⟩
  · rintro ⟨hr, ha⟩ z hz
    exact lt_of_le_of_ne (le_of_not_gt (hr z hz)) (ha z hz)

private theorem stable_of_count_le (p q : ℂ[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ComplexStable p) (hr : rightCount q ≤ rightCount p)
    (ha : ∀ z, z.re = 0 → q.rootMultiplicity z ≤ p.rootMultiplicity z) : ComplexStable q := by
  have hc : rightCount q = 0 := Nat.eq_zero_of_le_zero (by simpa [(complexStable_iff_counts p hp).mp h |>.1] using hr)
  have hh := (regionCount_zero_iff q hq (fun z => 0 < z.re)).mp hc
  intro z hz
  have hn : z.re ≤ 0 := le_of_not_gt (hh z hz)
  apply lt_of_le_of_ne hn
  intro he
  have hm := (rootMultiplicity_pos hq).mpr hz
  have hmp : 0 < p.rootMultiplicity z := hm.trans_le (ha z he)
  have hs := h z ((rootMultiplicity_pos hp).mp hmp)
  linarith

private theorem parity_not_stable (p : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hn : 0 < p.natDegree) : ¬ ComplexStable p := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hn))
  have hroot : p.IsRoot (-conj z) := by
    have he : (axisReflect p).eval (-conj z) = 0 := by
      change ((p.map (starRingEnd ℂ)).comp (-X)).eval (-conj z) = 0
      rw [eval_comp]
      simp only [eval_neg, eval_X, neg_neg]
      change (p.map (starRingEnd ℂ)).eval ((starRingEnd ℂ) z) = 0
      rw [eval_map_apply]
      change conj (p.eval z) = 0
      rw [hz, map_zero]
    rw [hp, eval_mul, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left hσ
  intro h
  have h₁ := h z hz
  have h₂ := h (-conj z) hroot
  simp only [Complex.neg_re, Complex.conj_re] at h₂
  linarith

private theorem encoded_pair_ne_zero (d : ℕ) (u v : Row ℝ) (hu : u 0 ≠ 0) :
    (encodeRow (d + 1) u + encodeRow d v).map Complex.ofRealHom ≠ 0 := by
  intro h
  have hh := congrArg (fun p : ℂ[X] => p.coeff (d + 1)) h
  simp [coeff_map, coeff_add, coeff_encodeRow] at hh
  exact hu hh

private theorem axis_eq_mul_I (z : ℂ) (hz : z.re = 0) : z = z.im * Complex.I := by
  apply Complex.ext <;> simp [hz]

private theorem le_of_repair_multiplicity {a b : ℕ} (P : Prop) [Decidable P]
    (h : a = if P then b else b - 1) : a ≤ b := by
  rw [h]
  split_ifs
  · exact le_rfl
  · exact Nat.sub_le _ _

private theorem encode_zero_of_empty (d w : ℕ) (r : Row ℝ) (hw : d / 2 < w)
    (hs : ∀ j, d < 2 * j → r j = 0) (hn : ¬ (nonzeroIndices w r).Nonempty) :
    encodeRow d r = 0 := by
  have hz (j : ℕ) : r j = 0 := by
    by_cases hj : j < w
    · by_contra hh
      exact hn ⟨j, by simp [nonzeroIndices, hj, hh]⟩
    · exact hs j (by omega)
  ext j
  simp [coeff_encodeRow, hz]

private theorem next_nonempty_of_stable (d w : ℕ) (upper lower : Row ℝ)
    (hv0 : lower 0 ≠ 0) (hw : d / 2 < w)
    (hu : ∀ j, d + 2 < 2 * j → upper j = 0)
    (hv : ∀ j, d + 1 < 2 * j → lower j = 0)
    (hs : ComplexStable ((encodeRow (d + 2) upper + encodeRow (d + 1) lower).map
      Complex.ofRealHom)) : (nonzeroIndices w (boundedNextRow w upper lower)).Nonempty := by
  by_contra hn
  let raw := boundedNextRow w upper lower
  have hr : ∀ j, d < 2 * j → raw j = 0 := by
    intro j hj
    dsimp [raw, boundedNextRow]
    split
    · exact nextRow_zero upper lower j (hu (j + 1) (by omega)) (hv (j + 1) (by omega))
    · rfl
  have hz := encode_zero_of_empty d w raw hw hr hn
  have he : encodeRow d (nextRow upper lower) = encodeRow d raw := by
    apply encodeRow_congr
    intro j hj
    simp [raw, boundedNextRow, show j < w by omega]
  have hrec := encodeRow_recurrence d upper lower hv0 hv
  rw [he, hz, add_zero] at hrec
  let V := (encodeRow (d + 1) lower).map Complex.ofRealHom
  have hdeg : V.natDegree = d + 1 := by simpa [V] using encodeRow_natDegree (d + 1) lower hv0
  apply parity_not_stable V ((-1 : ℂ) ^ (d + 1)) (pow_ne_zero _ (by norm_num))
    (encodeRow_axisReflect _ _) (by omega)
  intro z hz
  apply hs z
  rw [hrec]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    IsRoot, eval_add, eval_mul, eval_C, eval_X]
  change _ * z * V.eval z + V.eval z = 0
  rw [hz, mul_zero, add_zero]

private theorem linear_rightCount (a b : ℝ) (ha : a ≠ 0) :
    rightCount ((C a * X + C b).map Complex.ofRealHom) =
      if a / b < 0 then 1 else 0 := by
  have he : ((C a * X + C b).map Complex.ofRealHom) =
      C (a : ℂ) * (X - C ((-b / a : ℝ) : ℂ)) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      mul_sub, ← C_mul]
    have hh : (a : ℂ) * ((-b / a : ℝ) : ℂ) = -(b : ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr ha]
    rw [hh, C_neg]
    change C (a : ℂ) * X + C (b : ℂ) = C (a : ℂ) * X - -C (b : ℂ)
    ring
  rw [he, rightCount_mul (C_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ha))
    (X_sub_C_ne_zero _), rightCount_C, zero_add, rightCount_X_sub_C]
  have hsign : 0 < ((-b / a : ℝ) : ℂ).re ↔ a / b < 0 := by
    simp only [Complex.ofReal_re, neg_div, neg_pos, div_neg_iff]
    tauto
  simp only [hsign]


noncomputable def pairPolynomial (d : ℕ) (u v : Row ℝ) : ℂ[X] :=
  (encodeRow (d+1) u + encodeRow d v).map Complex.ofRealHom

/-- The counter already includes the crossing of the current pair. The axis
invariant applies precisely while the accumulated degeneracy flag is false. -/
structure LoopInvariant (p : ℝ[X]) (d : ℕ) (u v : Row ℝ) (count : ℕ) (deg : Bool) : Prop where
  upper_nonzero : u 0 ≠ 0
  lower_nonzero : v 0 ≠ 0
  upper_support : ∀ j, d+1 < 2*j → u j = 0
  lower_support : ∀ j, d < 2*j → v j = 0
  counted : rightCount (p.map Complex.ofRealHom) + (if u 0 / v 0 < 0 then 1 else 0) =
    count + rightCount (pairPolynomial d u v)
  axis : deg = false → ∀ ω : ℝ,
    (pairPolynomial d u v).rootMultiplicity (ω * Complex.I) =
      (p.map Complex.ofRealHom).rootMultiplicity (ω * Complex.I)
  stable : HurwitzStable p → deg = false ∧ ComplexStable (pairPolynomial d u v)

theorem LoopInvariant.advance {p : ℝ[X]} {d w count : ℕ} {deg : Bool} {u v : Row ℝ}
    (h : LoopInvariant p (d+1) u v count deg) (hw : d/2 < w) :
    let raw := boundedNextRow w u v
    let row := repairRow (d+1) w v raw
    LoopInvariant p d v row (count + if v 0 / row 0 < 0 then 1 else 0)
      (deg || !decide (nonzeroIndices w raw).Nonempty) := by
  dsimp only
  let raw := boundedNextRow w u v
  let row := repairRow (d+1) w v raw
  have hr : ∀ j, d < 2*j → raw j = 0 := by
    intro j hj
    dsimp [raw, boundedNextRow]
    split
    · exact nextRow_zero u v j (h.upper_support (j+1) (by omega)) (h.lower_support (j+1) (by omega))
    · rfl
  have hn : row 0 ≠ 0 := repairRow_pivot_ne_zero_of_previous (d+1) w v raw (by omega) h.lower_nonzero
  have hc := eliminationRepair_rightCount d w u v h.upper_nonzero h.lower_nonzero hw
    h.upper_support h.lower_support
  have hm := eliminationRepair_axis_rootMultiplicity d w u v h.upper_nonzero h.lower_nonzero hw
    h.upper_support h.lower_support
  change ∀ ω : ℝ, (pairPolynomial d v row).rootMultiplicity (ω * Complex.I) =
    if (nonzeroIndices w raw).Nonempty then
      (pairPolynomial (d+1) u v).rootMultiplicity (ω * Complex.I)
    else (pairPolynomial (d+1) u v).rootMultiplicity (ω * Complex.I) - 1 at hm
  change rightCount (pairPolynomial (d+1) u v) =
    rightCount (pairPolynomial d v row) + _ at hc
  change LoopInvariant p d v row (count + if v 0 / row 0 < 0 then 1 else 0)
    (deg || !decide (nonzeroIndices w raw).Nonempty)
  refine ⟨h.lower_nonzero, hn, h.lower_support, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact repairRow_support (d+1) w v raw (by simpa using hr) j (by omega)
  · have := h.counted
    omega
  · intro hg ω
    have hg' : deg = false ∧ (nonzeroIndices w raw).Nonempty := by simpa using hg
    have hm' : (pairPolynomial d v row).rootMultiplicity (ω * Complex.I) =
        (pairPolynomial (d+1) u v).rootMultiplicity (ω * Complex.I) := by
      simpa only [ite_eq_left hg'.2] using hm ω
    exact hm'.trans (h.axis hg'.1 ω)
  · intro hp
    obtain ⟨hg, hs⟩ := h.stable hp
    have hraw := next_nonempty_of_stable d w u v h.lower_nonzero hw h.upper_support h.lower_support hs
    change (nonzeroIndices w raw).Nonempty at hraw
    refine ⟨by simp [hg, hraw], ?_⟩
    apply stable_of_count_le (pairPolynomial (d+1) u v) (pairPolynomial d v row)
      (encoded_pair_ne_zero _ _ _ h.upper_nonzero) (encoded_pair_ne_zero d v row h.lower_nonzero) hs (by omega)
    intro z hz
    rw [axis_eq_mul_I z hz]
    exact le_of_repair_multiplicity _ (hm z.im)

theorem LoopInvariant.start (p : ℝ[X]) (hp : p ≠ 0) (hn : 0 < p.natDegree) :
    let n := p.natDegree
    let u := initialRow n (descendingCoefficients p) 0
    let raw := initialRow n (descendingCoefficients p) 1
    let v := repairRow n (width n) u raw
    LoopInvariant p (n-1) u v (if u 0 / v 0 < 0 then 1 else 0)
      (!decide (nonzeroIndices (width n) raw).Nonempty) := by
  dsimp only
  let n := p.natDegree
  let u := initialRow n (descendingCoefficients p) 0
  let raw := initialRow n (descendingCoefficients p) 1
  let v := repairRow n (width n) u raw
  have hd : n-1+1 = n := by dsimp [n]; omega
  have hu : u 0 ≠ 0 := by simpa [u, initialRow, descendingCoefficients, n] using leadingCoeff_ne_zero.mpr hp
  have hr : ∀ j, n-1 < 2*j → raw j = 0 := by
    intro j hj
    simp [raw, initialRow, show ¬ 2*j+1 ≤ n by omega]
  have hw : (n-1)/2 < width n := by dsimp [width]; omega
  have hc := repairRow_rightCount (n-1) (width n) u raw hu hw hr
  have hm := repairRow_axis_rootMultiplicity (n-1) (width n) u raw hu hw hr
  have he : encodeRow n u + encodeRow (n-1) raw = p := initial_polynomials p hn
  rw [hd, he] at hc
  have hm' (ω : ℝ) := hm ω
  simp only [hd, he] at hm'
  have hv : v 0 ≠ 0 := repairRow_pivot_ne_zero_of_previous n (width n) u raw (ne_of_gt hn) hu
  have hpC := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  change LoopInvariant p (n-1) u v (if u 0 / v 0 < 0 then 1 else 0)
    (!decide (nonzeroIndices (width n) raw).Nonempty)
  refine ⟨hu, hv, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp [u, initialRow, show ¬ 2*j ≤ n by omega]
  · exact repairRow_support n (width n) u raw hr
  · have hc' : rightCount (pairPolynomial (n-1) u v) = rightCount (p.map Complex.ofRealHom) := by
      simpa only [pairPolynomial, hd] using hc
    rw [hc']; omega
  · intro hg ω
    have hraw : (nonzeroIndices (width n) raw).Nonempty := by simpa using hg
    simpa only [pairPolynomial, hd, ite_eq_left hraw] using hm' ω
  · intro hs
    have hraw : (nonzeroIndices (width n) raw).Nonempty := by
      by_contra hz
      have hzero := encode_zero_of_empty (n-1) (width n) raw hw hr hz
      rw [hzero, add_zero] at he
      have hpar : axisReflect (p.map Complex.ofRealHom) = C ((-1 : ℂ)^n) * p.map Complex.ofRealHom := by
        rw [← he]; exact encodeRow_axisReflect _ _
      exact parity_not_stable _ _ (pow_ne_zero _ (by norm_num)) hpar (by simpa [n] using hn) hs
    refine ⟨by simp [hraw], ?_⟩
    apply stable_of_count_le (p.map Complex.ofRealHom) _ hpC
      (encoded_pair_ne_zero _ _ _ hu) hs
    · simpa only [pairPolynomial, hd] using hc.le
    · intro z hz
      rw [axis_eq_mul_I z hz]
      simpa only [pairPolynomial, hd, ite_eq_left hraw] using (hm' z.im).le

theorem LoopInvariant.finish {p : ℝ[X]} (hp : p ≠ 0) {u v : Row ℝ} {count : ℕ} {deg : Bool}
    (h : LoopInvariant p 0 u v count deg) :
    count = rightCount (p.map Complex.ofRealHom) ∧
      ((deg = false ∧ count = 0) ↔ HurwitzStable p) := by
  have hc : rightCount (pairPolynomial 0 u v) = if u 0 / v 0 < 0 then 1 else 0 := by
    simpa [pairPolynomial, encodeRow] using linear_rightCount (u 0) (v 0) h.upper_nonzero
  have hcount : count = rightCount (p.map Complex.ofRealHom) := by have := h.counted; omega
  refine ⟨hcount, ?_⟩
  have hpC := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  constructor
  · rintro ⟨hg, hz⟩
    apply (complexStable_iff_counts _ hpC).mpr
    refine ⟨hcount ▸ hz, ?_⟩
    apply (regionCount_zero_iff _ hpC (fun z => z.re = 0)).mpr
    intro z hz hzre
    have hnot : ¬ (pairPolynomial 0 u v).IsRoot z := by
      intro hh
      have hh := congrArg Complex.re hh
      simp [pairPolynomial, encodeRow, eval_add, eval_mul, eval_C, eval_X, Complex.mul_re, hzre] at hh
      exact h.lower_nonzero hh
    have hm := h.axis hg z.im
    rw [← axis_eq_mul_I z hzre, rootMultiplicity_eq_zero hnot] at hm
    have := (rootMultiplicity_pos hpC).mpr hz
    omega
  · intro hs
    exact ⟨(h.stable hs).1, hcount.trans ((complexStable_iff_counts _ hpC).mp hs).1⟩

end RouthHurwitz
