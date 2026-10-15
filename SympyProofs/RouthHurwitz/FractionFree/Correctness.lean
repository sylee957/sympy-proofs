import SympyProofs.RouthHurwitz.FractionFree.Loop
import SympyProofs.RouthHurwitz.Table.Invariant
import Std.Tactic.Do
import Std.WP

/-! Root-count and stability correctness obtained from initialization,
preservation, and termination of the actual imperative loop. -/
namespace RouthHurwitz.FractionFree
open Polynomial Imperative Imperative.Bounds Proofs

private def scale {W : ℕ} (c : ℝ) (row : Vector ℝ W) : Vector ℝ W := row.map (c * ·)

/-- Scales are witnesses used only by the proof, not runtime state. -/
private def Scaled {W : ℕ} (row spec : Vector ℝ W) : Prop :=
  ∃ c : ℝ, 0 < c ∧ row = scale c spec

private theorem scaled_refl {W : ℕ} (row : Vector ℝ W) : Scaled row row := by
  exact ⟨1, zero_lt_one, by simp [scale]⟩

private theorem scan_scale {W : ℕ} (w : Fin (W + 1)) (c : ℝ) (hc : c ≠ 0)
    (row : Vector ℝ W) : scan w (scale c row) = scan w row := by
  simp [scan, scale, hc]

private theorem repair_scaled {W : ℕ} (d : ℕ) (w : Fin (W + 2))
    {upper raw u r : Vector ℝ (W + 1)} (hu : Scaled upper u) (hr : Scaled raw r) :
    Scaled (repair d w upper raw).1 (repair d w u r).1 ∧
    (repair d w upper raw).2 = (repair d w u r).2 := by
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hr
  simp only [repair]
  simp only [scan_scale w b (ne_of_gt hb)]
  simp only [scale, Vector.getElem_map, mul_eq_zero, ne_of_gt hb, false_or]
  split_ifs
  all_goals simp only [Id.run_pure, and_true]
  · refine ⟨b, hb, ?_⟩
    apply Vector.ext
    intro j hj
    simp only [scale, Vector.getElem_ofFn, Vector.getElem_map]
    split_ifs <;> ring
  · exact ⟨b, hb, rfl⟩
  · refine ⟨a, ha, ?_⟩
    apply Vector.ext
    intro j hj
    simp only [scale, Vector.getElem_ofFn, Vector.getElem_map]
    ring

private theorem scaled_crossing {W : ℕ} {upper lower u l : Vector ℝ (W + 1)}
    (hu : Scaled upper u) (hl : Scaled lower l) :
    (upper[0] * lower[0] < 0) ↔ u[0] / l[0] < 0 := by
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hl
  simp [scale, mul_neg_iff, div_neg_iff, ha, hb, not_lt_of_gt ha, not_lt_of_gt hb]

private theorem scaled_pivot {W : ℕ} {row spec : Vector ℝ (W + 1)}
    (h : Scaled row spec) (hs : spec[0] ≠ 0) : row[0] ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simpa [scale] using mul_ne_zero (ne_of_gt hc) hs

private theorem elimination_scaled (n k : ℕ) (upper lower : Vector ℝ (width n))
    (u l : ℕ → ℝ) (d : ℝ) (hd : 0 < d) (hl0 : l 0 ≠ 0)
    (hu : Scaled upper (tabulate (width n) u))
    (hl : Scaled lower (tabulate (width n) l)) :
    Scaled (Vector.ofFn (fun j : Fin (width n) =>
      if hj : j.val < activeWidth n (k + 2) then
        (if lower[0]'(width_pos _) < 0 then (-1 : ℝ) else 1) *
          (lower[0]'(width_pos _) * upper[j.val + 1]'(next_index_lt n k j.val hj) -
            upper[0]'(width_pos _) * lower[j.val + 1]'(next_index_lt n k j.val hj)) / d
      else 0))
      (tabulate (width n) (boundedNextRow (activeWidth n (k + 2)) u l)) := by
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hl
  refine ⟨a * |b * l 0| / d, div_pos (mul_pos ha (abs_pos.mpr (mul_ne_zero (ne_of_gt hb) hl0))) hd, ?_⟩
  apply Vector.ext
  intro j hj
  simp only [scale, tabulate, Vector.getElem_ofFn, Vector.getElem_map, boundedNextRow, nextRow]
  split_ifs with hj' hs
  · rw [abs_of_neg hs]
    field_simp
  · rw [abs_of_nonneg (le_of_not_gt hs)]
    field_simp
  · simp

open scoped Std.WP in
private theorem run_outcome (p : Polynomial ℝ) (hp : p ≠ 0) :
    (Exact.run p).signChanges = rightCount (p.map Complex.ofRealHom) ∧
      (((Exact.run p).degenerate = false ∧ (Exact.run p).signChanges = 0) ↔ HurwitzStable p) := by
  by_cases hn : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hn
    have hc : p.coeff 0 ≠ 0 := by
      simpa [Polynomial.leadingCoeff, hn] using leadingCoeff_ne_zero.mpr hp
    rw [he]
    simp [Exact.run, hc, HurwitzStable]
  · generalize h : Exact.run p = result
    apply Std.WP.Id.of_run_eq_wp h
    vcgen invariants
    · fun pref _ ⟨upper, lower, _, count, degenerate, divisor, nextDivisor⟩ =>
        ∃ u v : Row ℝ,
          Scaled upper (tabulate (width p.natDegree) u) ∧
          Scaled lower (tabulate (width p.natDegree) v) ∧
          LoopInvariant p (p.natDegree-(pref.length+1)) u v count degenerate ∧
          0 < divisor ∧ 0 < nextDivisor
    case vc1 => exact (hn ‹_ = 0›).elim
    case vc2 =>
      have h0 := rowFunction_initial p 0
      have h1 := rowFunction_initial p 1
      dsimp only [width, initial] at h0 h1
      simp +zetaDelta only [repair_eq, h0, h1]
      let u := initialRow p.natDegree (descendingCoefficients p) 0
      let v := repairRow p.natDegree (width p.natDegree) u
        (initialRow p.natDegree (descendingCoefficients p) 1)
      refine ⟨u, v, scaled_refl _, scaled_refl _, ?_, zero_lt_one, zero_lt_one⟩
      have h := LoopInvariant.start p hp (by omega)
      simpa [u, v, initial, initialCoefficients, initialRow, descendingCoefficients, tabulate,
        mul_neg_iff, div_neg_iff] using h
    case vc3 =>
      obtain ⟨u, v, _, _, hm, _, _⟩ := ‹∃ u v : Row ℝ, _›
      simp only [List.length_range] at hm
      rw [show p.natDegree - (p.natDegree - 1 + 1) = 0 by omega] at hm
      exact hm.finish hp
    case vc4 =>
      rename_i pref k suff hsplit up lo rs cnt dg dv nd hi _ _ _ _ _
      obtain ⟨hkpos, hlt⟩ := range_split hsplit
      have hk : k+2 ≤ p.natDegree := by omega
      simp only [← hkpos] at hi
      simp only [List.length_append, List.length_singleton, ← hkpos]
      let n := p.natDegree
      obtain ⟨u, v, hu, hl, hm, hd, hnext⟩ := hi
      let w : Fin (width n + 1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
      let raw := Vector.ofFn (fun j : Fin (width n) =>
        if hj : j.val < w then
          (if lo[0]'(width_pos _) < 0 then (-1 : ℝ) else 1) *
            (lo[0]'(width_pos _) * up[j.val+1]'(next_index_lt n k j.val hj) -
              up[0]'(width_pos _) * lo[j.val+1]'(next_index_lt n k j.val hj)) / dv
        else 0)
      let r := boundedNextRow (activeWidth n (k+2)) u v
      let v' := repairRow (n+1-(k+2)) (activeWidth n (k+2)) v r
      have hr := elimination_scaled n k up lo u v dv hd hm.lower_nonzero hu hl
      change Scaled raw (tabulate (width n) r) at hr
      have hrepair := repair_scaled (n+1-(k+2)) w hl hr
      have hv := rowFunction_tabulate_degree n (n-(k+1)) v (by omega) hm.lower_support
      have hz : rowFunction (tabulate (width n) r) = r := by
        apply rowFunction_tabulate
        intro j hj
        simp [r, boundedNextRow, show ¬ j < activeWidth n (k+2) by dsimp [activeWidth]; omega]
      dsimp only [width] at hv hz
      have heq := repair_eq (n+1-(k+2)) w (tabulate (width n) v) (tabulate (width n) r)
      dsimp only [width] at heq hrepair
      simp only [hv, hz] at heq
      rw [heq] at hrepair
      dsimp only at hrepair
      have hcross := scaled_crossing hl hrepair.1
      have hl0 : lo[0]'(width_pos _) ≠ 0 := by
        apply scaled_pivot hl
        simpa only [tabulate, Vector.getElem_ofFn] using hm.lower_nonzero
      simp only [tabulate, Vector.getElem_ofFn] at hcross
      have hdegree : n-(k+2)+1 = n-(k+1) := by dsimp [n]; omega
      have hm' : LoopInvariant p (n-(k+2)+1) u v cnt dg := by rwa [hdegree]
      have hnew := hm'.advance (w := activeWidth n (k+2)) (by dsimp [activeWidth, width]; omega)
      have hdegree' : n-(k+2)+1 = n+1-(k+2) := by dsimp [n]; omega
      simp only [hdegree'] at hnew
      change LoopInvariant p (n-(k+2)) v v'
        (cnt + if v 0 / v' 0 < 0 then 1 else 0)
        (dg || !decide (nonzeroIndices (activeWidth n (k+2)) r).Nonempty) at hnew
      refine ⟨v, v', hl, hrepair.1, ?_, ?_⟩
      · change (lo[0]'(width_pos _) * (repair (n+1-(k+2)) w lo raw).1[0] < 0) ↔
          v 0 / v' 0 < 0 at hcross
        have hcount : (cnt + if lo[0]'(width_pos _) * (repair (n+1-(k+2)) w lo raw).1[0] < 0 then 1 else 0) =
            cnt + if v 0 / v' 0 < 0 then 1 else 0 := by
          congr 1
          exact if_congr hcross rfl rfl
        change LoopInvariant p (n-(k+2)) v v'
          (cnt + if lo[0]'(width_pos _) * (repair (n+1-(k+2)) w lo raw).1[0] < 0 then 1 else 0)
          (dg || !(repair (n+1-(k+2)) w lo raw).2)
        rw [hcount, hrepair.2]
        exact hnew
      · dsimp only [divisor, nextDivisor]
        split_ifs
        · exact ⟨zero_lt_one, zero_lt_one⟩
        · exact ⟨hnext, abs_pos.mpr hl0⟩

/-- The stored counter counts open-right-half-plane roots with multiplicity. -/
theorem real_run_signChanges_correct (p : Polynomial ℝ) (hp : p ≠ 0) :
    (Exact.run p).signChanges = rightCount (p.map Complex.ofRealHom) :=
  (run_outcome p hp).1

/-- Acceptance is equivalent to strict stability, including rejection of zero. -/
theorem accepts_real_run_iff_hurwitzStable (p : Polynomial ℝ) :
    accepts (Exact.run p) = true ↔ HurwitzStable p := by
  by_cases hp : p = 0
  · subst p
    simp [Exact.Proofs.run_eq, accepts, HurwitzStable]
    exact ⟨0, by simp⟩
  · simpa only [accepts, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq]
      using (run_outcome p hp).2

end RouthHurwitz.FractionFree
