import SympyProofs.RouthHurwitz.Imperative.Rows
import SympyProofs.RouthHurwitz.Table.Invariant

/-! Direct semantic invariants for the ordinary imperative loop. -/
namespace RouthHurwitz.Imperative
open Polynomial Bounds
namespace Proofs

variable {K : Type*} [Field K] [LinearOrder K]

-- These proof-only expressions describe Lean's tuple of mutable loop locals.
-- They are used only in the proof and are never called by `run`.
noncomputable def initialLocals (p : Polynomial K) :
    Vector K (width p.natDegree) × Vector K (width p.natDegree) × List (Vector K (width p.natDegree)) × ℕ × Bool := Id.run do
  let upper := initial p 0
  let raw := initial p 1
  let (lower, valid) : Vector K (width p.natDegree) × Bool := repair p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩ upper raw
  return (upper, lower, [upper, lower],
    if upper[0]'(width_pos _) / lower[0]'(width_pos _) < 0 then 1 else 0, !valid)

noncomputable def step (n k : ℕ) (locals : Vector K (width n) × Vector K (width n) × List (Vector K (width n)) × ℕ × Bool) :
    Vector K (width n) × Vector K (width n) × List (Vector K (width n)) × ℕ × Bool := Id.run do
  let (upper, lower, rows, count, degenerate) := locals
  let w : Fin (width n + 1) := ⟨activeWidth n (k + 2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (lower[0]'(width_pos _) * upper[j.val + 1]'(next_index_lt n k j.val hj) -
        upper[0]'(width_pos _) * lower[j.val + 1]'(next_index_lt n k j.val hj)) / lower[0]'(width_pos _)
    else 0)
  let (row, valid) : Vector K (width n) × Bool := repair (n + 1 - (k + 2)) w lower raw
  return (lower, row, List.append rows [row],
    count + if lower[0]'(width_pos _) / row[0]'(width_pos _) < 0 then 1 else 0, degenerate || !valid)


abbrev Locals (n : ℕ) := Vector ℝ (width n) × Vector ℝ (width n) ×
  List (Vector ℝ (width n)) × ℕ × Bool

def Inv (p : Polynomial ℝ) (k : ℕ) (s : Locals p.natDegree) : Prop :=
  LoopInvariant p (p.natDegree-(k+1)) (rowFunction s.1) (rowFunction s.2.1) s.2.2.2.1 s.2.2.2.2

private theorem initial_inv (p : Polynomial ℝ) (hp : p ≠ 0) (hn : 0 < p.natDegree) :
    Inv p 0 (initialLocals p) := by
  have h0 := rowFunction_initial p 0
  have h1 := rowFunction_initial p 1
  let u := initialRow p.natDegree (descendingCoefficients p) 0
  let v := repairRow p.natDegree (width p.natDegree) u
    (initialRow p.natDegree (descendingCoefficients p) 1)
  have h := LoopInvariant.start p hp hn
  change LoopInvariant p (p.natDegree-1) u v _ _ at h
  have hv := rowFunction_tabulate_degree p.natDegree (p.natDegree-1) v (by omega) h.lower_support
  dsimp only [width] at h0 h1 hv
  simp only [Inv, initialLocals, repair_eq, h0, h1, Id.run_pure]
  rw [rowFunction_initial]
  change LoopInvariant p (p.natDegree-1) u (rowFunction (tabulate (p.natDegree / 2 + 1) v)) _ _
  rw [hv]
  simpa [initial, initialCoefficients, initialRow, descendingCoefficients, tabulate, u, v] using h

private theorem step_inv (p : Polynomial ℝ) (k : ℕ) (hk : k+2 ≤ p.natDegree)
    (s : Locals p.natDegree) (h : Inv p k s) : Inv p (k+1) (step p.natDegree k s) := by
  let n := p.natDegree
  obtain ⟨upper, lower, rows, count, deg⟩ := s
  change LoopInvariant p (n-(k+1)) (rowFunction upper) (rowFunction lower) count deg at h
  let w : Fin (width n + 1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
        upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj)) / lower[0]'(width_pos _)
    else 0)
  have hraw : rowFunction raw = boundedNextRow w (rowFunction upper) (rowFunction lower) := by
    funext j
    by_cases hj : j < activeWidth n (k+2)
    · have hj' := next_index_lt n k j hj
      dsimp only [n] at hj hj'
      simp [raw, w, n, rowFunction, hj, show j < width p.natDegree by omega, hj', boundedNextRow, nextRow, width_pos]
    · simp only [rowFunction, raw, Vector.getElem_ofFn, boundedNextRow]
      split_ifs <;> simp_all
  have hs : ∀ j, n-(k+2) < 2*j → rowFunction raw j = 0 := by
    rw [hraw]
    intro j hj
    dsimp [boundedNextRow]
    split
    · exact nextRow_zero _ _ j (h.upper_support (j+1) (by omega)) (h.lower_support (j+1) (by omega))
    · rfl
  have hd : n+1-(k+2)-1 = n-(k+2) := by dsimp [n]; omega
  have he := repair_function n (n+1-(k+2)) w lower raw (by omega) (by rw [hd]; exact hs)
  let row := (repair (n+1-(k+2)) w lower raw).1
  have hv0 : lower[0]'(width_pos _) = rowFunction lower 0 := by simp [rowFunction, width_pos]
  have hr0 : row[0]'(width_pos _) = rowFunction row 0 := by
    simp only [rowFunction]
    split_ifs
    · rfl
    · omega
  have hf := congrArg Prod.snd (repair_eq (n+1-(k+2)) w lower raw)
  dsimp only at hf
  have hdegree : n-(k+2)+1 = n-(k+1) := by dsimp [n]; omega
  have h' : LoopInvariant p (n-(k+2)+1) (rowFunction upper) (rowFunction lower) count deg := by rwa [hdegree]
  have hnew := h'.advance (w := w) (by dsimp [w, activeWidth, width]; omega)
  have hdegree' : n-(k+2)+1 = n+1-(k+2) := by dsimp [n]; omega
  simp only [hdegree'] at hnew
  change LoopInvariant p (n-(k+1+1)) (rowFunction lower) (rowFunction row)
    (count + if lower[0]'(width_pos _) / row[0]'(width_pos _) < 0 then 1 else 0)
    (deg || !(repair (n+1-(k+2)) w lower raw).2)
  change rowFunction row = _ at he
  rw [hv0, hr0, he, hf, hraw]
  dsimp only [width] at hraw hnew ⊢
  simp only [hraw, show k+1+1 = k+2 by omega]
  exact hnew

theorem loop_invariant (p : Polynomial ℝ) (hp : p ≠ 0) (k : ℕ) (hk : k+1 ≤ p.natDegree) :
    Inv p k ((List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)) := by
  induction k with
  | zero => simpa using initial_inv p hp (by omega)
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_inv p k (by omega) _ (ih (by omega))

end Proofs
end RouthHurwitz.Imperative
