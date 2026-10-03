import SympyProofs.RouthHurwitz.Imperative.Basic
import SympyProofs.RouthHurwitz.Table.Polynomial

/-! Finite-row interpretation and the local repair correspondence. -/
namespace RouthHurwitz.Imperative

variable {K : Type*} [Field K] [DecidableEq K]

open Bounds

/-- Proof-only zero extension connecting finite rows to the mathematical specification.
The executable algorithm uses bounded vector indexing instead. -/
def rowFunction {W : ℕ} (row : Vector K W) (j : ℕ) : K :=
  if h : j < W then row[j] else 0

/-- Sample a mathematical row at its fixed finite width. -/
def tabulate (W : ℕ) (f : ℕ → K) : Vector K W := Vector.ofFn (fun j => f j)

omit [DecidableEq K] in
theorem rowFunction_tabulate (W : ℕ) (f : ℕ → K) (h : ∀ j, W ≤ j → f j = 0) :
    rowFunction (tabulate W f) = f := by
  funext j
  unfold rowFunction
  split_ifs with hj
  · simp [tabulate]
  · exact (h j (by omega)).symm

private theorem scan_found {W : ℕ} (w : Fin (W + 1)) (raw : Vector K W)
    (h : (nonzeroIndices w (rowFunction raw)).Nonempty) :
    scan w raw = firstNonzero w (rowFunction raw) := by
  have hk := firstNonzero_spec w (rowFunction raw) h
  apply (List.findIdx_eq (by simpa using hk.1)).mpr
  constructor
  · simpa [rowFunction, show firstNonzero w (rowFunction raw) < W by omega] using hk.2
  · intro j hj
    have hz := before_firstNonzero w (rowFunction raw) h j hj
    simpa [rowFunction, show j < W by omega] using hz

private theorem scan_missing {W : ℕ} (w : Fin (W + 1)) (raw : Vector K W)
    (h : ¬ (nonzeroIndices w (rowFunction raw)).Nonempty) : scan w raw = w.val := by
  have hh : ∀ j ∈ List.finRange w.val, decide (raw[j.val]'(by omega) ≠ 0) = false := by
    intro j hj
    have hz : raw[j.val]'(by omega) = 0 := by
      by_contra hn
      apply h
      exact ⟨j.val, by simp [nonzeroIndices, rowFunction, j.isLt,
        show j.val < W by omega, hn]⟩
    simp [hz]
  simpa [scan] using List.findIdx_eq_length.mpr hh

theorem repair_eq {W : ℕ} (d : ℕ) (w : Fin (W + 2)) (previous raw : Vector K (W + 1)) :
    repair d w previous raw =
      (tabulate (W + 1) (repairRow d w (rowFunction previous) (rowFunction raw)),
       decide (nonzeroIndices w (rowFunction raw)).Nonempty) := by
  by_cases hn : (nonzeroIndices w (rowFunction raw)).Nonempty
  · have hk := firstNonzero_spec w (rowFunction raw) hn
    by_cases hz : raw[0] = 0
    · simp only [repair, scan_found w raw hn, if_pos hk.1, Id.run_pure,
        repairRow, if_pos hn, rowFunction, dif_pos (Nat.zero_lt_succ W), if_pos hz, decide_eq_true hn, Prod.mk.injEq,
        and_true]
      apply Vector.ext
      intro j hj
      simp [tabulate, shiftRow, rowFunction]
      split_ifs <;> simp_all
      all_goals omega
    · simp only [repair, scan_found w raw hn, if_pos hk.1, Id.run_pure,
        repairRow, if_pos hn, rowFunction, dif_pos (Nat.zero_lt_succ W), if_neg hz, decide_eq_true hn, Prod.mk.injEq,
        and_true]
      apply Vector.ext
      intro j hj
      simp only [tabulate, Vector.getElem_ofFn, rowFunction, dif_pos hj]
  · simp only [repair, scan_missing w raw hn, lt_self_iff_false, if_false, Id.run_pure,
      repairRow, if_neg hn, decide_eq_false hn, Prod.mk.injEq, and_true]
    apply Vector.ext
    intro j hj
    simp only [tabulate, Vector.getElem_ofFn, derivativeRow, rowFunction, dif_pos hj]

omit [DecidableEq K] in
private theorem initial_eq (p : Polynomial K) (parity : ℕ) :
    initial p parity = tabulate (width p.natDegree) (initialRow p.natDegree (descendingCoefficients p) parity) := by
  rfl

omit [DecidableEq K] in
theorem rowFunction_initial (p : Polynomial K) (parity : ℕ) :
    rowFunction (initial p parity) = initialRow p.natDegree (descendingCoefficients p) parity := by
  rw [initial_eq]
  apply rowFunction_tabulate
  intro j hj
  have hh : ¬ 2 * j + parity ≤ p.natDegree := by dsimp [width] at hj; omega
  simp [initialRow, hh]

omit [DecidableEq K] in
/-- Zero extension recovers a degree-padded mathematical row. -/
theorem rowFunction_tabulate_degree (n d : ℕ) (u : Row K) (hd : d ≤ n)
    (hu : ∀ j, d < 2*j → u j = 0) :
    rowFunction (tabulate (width n) u) = u := by
  apply rowFunction_tabulate
  intro j hj
  apply hu
  dsimp [width] at hj
  omega

/-- Zero extension of a repaired finite row agrees with the mathematical repair. -/
theorem repair_function (n d : ℕ) (w : Fin (width n + 1))
    (upper raw : Vector K (width n)) (hd : d-1 ≤ n)
    (hr : ∀ j, d-1 < 2*j → rowFunction raw j = 0) :
    rowFunction (repair d w upper raw).1 = repairRow d w (rowFunction upper) (rowFunction raw) := by
  rw [repair_eq]
  exact rowFunction_tabulate_degree n (d-1) _ hd (repairRow_support d w _ _ hr)

end RouthHurwitz.Imperative
