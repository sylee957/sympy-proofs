import SympyProofs.RouthHurwitz.Imperative.Rows
import SympyProofs.RouthHurwitz.Table.Invariant
import Std.Tactic.Do
import Std.WP

/-! Root-count and stability correctness obtained from initialization,
preservation, and termination of the actual imperative loop. -/
namespace RouthHurwitz.Imperative
open Polynomial Bounds

open scoped Std.WP in
private theorem run_outcome (p : Polynomial ℝ) (hp : p ≠ 0) :
    (run p).signChanges = rightCount (p.map Complex.ofRealHom) ∧
      (((run p).degenerate = false ∧ (run p).signChanges = 0) ↔ HurwitzStable p) := by
  by_cases hn : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hn
    have hc : p.coeff 0 ≠ 0 := by
      simpa [Polynomial.leadingCoeff, hn] using leadingCoeff_ne_zero.mpr hp
    rw [he]
    simp [run, hc, HurwitzStable]
  · generalize h : run p = result
    apply Std.WP.Id.of_run_eq_wp h
    vcgen [run, hn] invariants
    · fun pref _ ⟨upper, lower, _, count, degenerate⟩ =>
        LoopInvariant p (p.natDegree-(pref.length+1))
          (rowFunction upper) (rowFunction lower) count degenerate
    case vc1 => exact (hn ‹_ = 0›).elim
    case vc2 =>
      have h0 := rowFunction_initial p 0
      have h1 := rowFunction_initial p 1
      let u := initialRow p.natDegree (descendingCoefficients p) 0
      let v := repairRow p.natDegree (width p.natDegree) u
        (initialRow p.natDegree (descendingCoefficients p) 1)
      have h := LoopInvariant.start p hp (by omega)
      change LoopInvariant p (p.natDegree-1) u v _ _ at h
      have hv := rowFunction_tabulate_degree p.natDegree (p.natDegree-1) v (by omega) h.lower_support
      dsimp only [width] at h0 h1 hv
      simp +zetaDelta only [repair_eq, h0, h1]
      change LoopInvariant p (p.natDegree-1) u (rowFunction (tabulate (p.natDegree / 2 + 1) v)) _ _
      rw [hv]
      simpa [initial, initialCoefficients, initialRow, descendingCoefficients, tabulate, u, v] using h
    case vc3 =>
      have hi := ‹LoopInvariant p _ _ _ _ _›
      simp only [List.length_range] at hi
      rw [show p.natDegree - (p.natDegree - 1 + 1) = 0 by omega] at hi
      exact hi.finish hp
    case vc4 =>
      rename_i pref k suff hsplit u v rs c dg hi _ _ _
      obtain ⟨hkpos, hlt⟩ := range_split hsplit
      have hk : k+2 ≤ p.natDegree := by omega
      rw [← hkpos] at hi
      simp only [List.length_append, List.length_singleton, ← hkpos]
      let n := p.natDegree
      change LoopInvariant p (n-(k+1)) (rowFunction u) (rowFunction v) c dg at hi
      let w : Fin (width n + 1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
      let raw := Vector.ofFn (fun j : Fin (width n) =>
        if hj : j.val < w then
          (v[0]'(width_pos _) * u[j.val+1]'(next_index_lt n k j.val hj) -
            u[0]'(width_pos _) * v[j.val+1]'(next_index_lt n k j.val hj)) / v[0]'(width_pos _)
        else 0)
      have hraw : rowFunction raw = boundedNextRow w (rowFunction u) (rowFunction v) := by
        funext j
        by_cases hj : j < activeWidth n (k+2)
        · have hj' := next_index_lt n k j hj
          dsimp only [n] at hj hj'
          simp +zetaDelta [rowFunction, hj, show j < width p.natDegree by omega, hj', boundedNextRow, nextRow]
        · simp only [rowFunction, raw, Vector.getElem_ofFn, boundedNextRow]
          split_ifs <;> simp_all
      have hs : ∀ j, n-(k+2) < 2*j → rowFunction raw j = 0 := by
        rw [hraw]
        intro j hj
        dsimp [boundedNextRow]
        split
        · exact nextRow_zero _ _ j (hi.upper_support (j+1) (by omega)) (hi.lower_support (j+1) (by omega))
        · rfl
      have hd : n+1-(k+2)-1 = n-(k+2) := by dsimp [n]; omega
      have he := repair_function n (n+1-(k+2)) w v raw (by omega) (by rw [hd]; exact hs)
      let row := (repair (n+1-(k+2)) w v raw).1
      have hv0 : v[0]'(width_pos _) = rowFunction v 0 := by simp [rowFunction]
      have hr0 : row[0]'(width_pos _) = rowFunction row 0 := by
        simp only [rowFunction]
        split_ifs
        · rfl
        · omega
      have hf := congrArg Prod.snd (repair_eq (n+1-(k+2)) w v raw)
      dsimp only at hf
      have hdegree : n-(k+2)+1 = n-(k+1) := by dsimp [n]; omega
      have h' : LoopInvariant p (n-(k+2)+1) (rowFunction u) (rowFunction v) c dg := by rwa [hdegree]
      have hnew := h'.advance (w := w) (by dsimp [w, activeWidth, width]; omega)
      have hdegree' : n-(k+2)+1 = n+1-(k+2) := by dsimp [n]; omega
      simp only [hdegree'] at hnew
      change LoopInvariant p (n-(k+1+1)) (rowFunction v) (rowFunction row)
        (c + if v[0]'(width_pos _) / row[0]'(width_pos _) < 0 then 1 else 0)
        (dg || !(repair (n+1-(k+2)) w v raw).2)
      change rowFunction row = _ at he
      rw [hv0, hr0, he, hf, hraw]
      dsimp only [width] at hraw hnew ⊢
      simp only [show k+1+1 = k+2 by omega]
      exact hnew

/-- The stored counter counts open-right-half-plane roots with multiplicity. -/
theorem run_signChanges_correct (p : Polynomial ℝ) (hp : p ≠ 0) :
    (run p).signChanges = rightCount (p.map Complex.ofRealHom) :=
  (run_outcome p hp).1

/-- Acceptance is equivalent to strict stability, including rejection of zero. -/
theorem accepts_iff_hurwitzStable (p : Polynomial ℝ) :
    accepts (run p) = true ↔ HurwitzStable p := by
  by_cases hp : p = 0
  · subst p
    simp [run, accepts, HurwitzStable]
    exact ⟨0, by simp⟩
  · simpa only [accepts, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq]
      using (run_outcome p hp).2

end RouthHurwitz.Imperative
