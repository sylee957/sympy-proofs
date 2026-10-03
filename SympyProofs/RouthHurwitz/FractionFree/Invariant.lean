import SympyProofs.RouthHurwitz.FractionFree.Loop
import SympyProofs.RouthHurwitz.Table.Invariant

/-! Direct mathematical loop invariants for the fraction-free runner.
`Proofs` contains shared proof-only descriptions of the mutable locals. -/
namespace RouthHurwitz.FractionFree
open Polynomial Imperative Imperative.Bounds

namespace Proofs

def scale {W : ℕ} (c : ℝ) (row : Vector ℝ W) : Vector ℝ W := row.map (c * ·)

/-- Scales are witnesses used only by the proof, not runtime state. -/
def Scaled {W : ℕ} (row spec : Vector ℝ W) : Prop :=
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

theorem scaled_pivot {W : ℕ} {row spec : Vector ℝ (W + 1)}
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

/-- Witnesses normalize only the current two rows; they are not a second
algorithm or a stored table. The invariant describes roots and diagnostics. -/
def Inv (p : Polynomial ℝ) (k : ℕ) (s : Locals (K := ℝ) p.natDegree) : Prop :=
  ∃ u v : Row ℝ,
    Scaled s.1 (tabulate (width p.natDegree) u) ∧
    Scaled s.2.1 (tabulate (width p.natDegree) v) ∧
    LoopInvariant p (p.natDegree-(k+1)) u v s.2.2.2.1 s.2.2.2.2.1 ∧
    0 < s.2.2.2.2.2.1 ∧ 0 < s.2.2.2.2.2.2

private theorem initial_inv (p : Polynomial ℝ) (hp : p ≠ 0) (hn : 0 < p.natDegree) :
    Inv p 0 (initialLocals p) := by
  have h0 := rowFunction_initial p 0
  have h1 := rowFunction_initial p 1
  dsimp only [width] at h0 h1
  simp only [initialLocals_eq, repair_eq, h0, h1, Id.run_pure]
  let u := initialRow p.natDegree (descendingCoefficients p) 0
  let v := repairRow p.natDegree (width p.natDegree) u
    (initialRow p.natDegree (descendingCoefficients p) 1)
  refine ⟨u, v, scaled_refl _, scaled_refl _, ?_, zero_lt_one, zero_lt_one⟩
  have h := LoopInvariant.start p hp hn
  simpa [u, v, initial, initialCoefficients, initialRow, descendingCoefficients, tabulate,
    mul_neg_iff, div_neg_iff] using h

private theorem step_inv (p : Polynomial ℝ) (k : ℕ) (hk : k+2 ≤ p.natDegree)
    (s : Locals (K := ℝ) p.natDegree) (hs : Inv p k s) :
    Inv p (k+1) (step p.natDegree k s) := by
  let n := p.natDegree
  obtain ⟨upper, lower, rows, count, degenerate, divisor, nextDivisor⟩ := s
  obtain ⟨u, v, hu, hl, hm, hd, hnext⟩ := hs
  dsimp only at hu hl hm hd hnext
  let w : Fin (width n + 1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (if lower[0]'(width_pos _) < 0 then (-1 : ℝ) else 1) *
        (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
          upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj)) / divisor
    else 0)
  let r := boundedNextRow (activeWidth n (k+2)) u v
  let v' := repairRow (n+1-(k+2)) (activeWidth n (k+2)) v r
  have hr := elimination_scaled n k upper lower u v divisor hd hm.lower_nonzero hu hl
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
  have hl0 : lower[0]'(width_pos _) ≠ 0 := by
    dsimp only [width] at hl ⊢
    apply scaled_pivot hl
    simpa only [tabulate, Vector.getElem_ofFn] using hm.lower_nonzero
  dsimp only [width] at hcross
  simp only [tabulate, Vector.getElem_ofFn] at hcross
  have hdegree : n-(k+2)+1 = n-(k+1) := by dsimp [n]; omega
  have hm' : LoopInvariant p (n-(k+2)+1) u v count degenerate := by rwa [hdegree]
  have hnew := hm'.advance (w := activeWidth n (k+2)) (by dsimp [activeWidth, width]; omega)
  have hdegree' : n-(k+2)+1 = n+1-(k+2) := by dsimp [n]; omega
  simp only [hdegree'] at hnew
  change LoopInvariant p (n-(k+2)) v v'
    (count + if v 0 / v' 0 < 0 then 1 else 0)
    (degenerate || !decide (nonzeroIndices (activeWidth n (k+2)) r).Nonempty) at hnew
  change Inv p (k+1)
    (lower, (repair (n+1-(k+2)) w lower raw).1,
      List.append rows [(repair (n+1-(k+2)) w lower raw).1],
      count + (if lower[0]'(width_pos _) * (repair (n+1-(k+2)) w lower raw).1[0] < 0 then 1 else 0),
      degenerate || !(repair (n+1-(k+2)) w lower raw).2,
      (if raw[0]'(width_pos _) = 0 then 1 else nextDivisor),
      (if raw[0]'(width_pos _) = 0 then 1 else |lower[0]'(width_pos _)|))
  refine ⟨v, v', hl, hrepair.1, ?_, ?_⟩
  · dsimp only at ⊢
    change (lower[0]'(width_pos _) * (repair (n+1-(k+2)) w lower raw).1[0] < 0) ↔
      v 0 / v' 0 < 0 at hcross
    have hcount : (count + if lower[0]'(width_pos _) * (repair (n+1-(k+2)) w lower raw).1[0] < 0 then 1 else 0) =
        count + if v 0 / v' 0 < 0 then 1 else 0 := by
      congr 1
      exact if_congr hcross rfl rfl
    dsimp only [width] at hcount hrepair ⊢
    rw [hcount, hrepair.2]
    exact hnew
  · dsimp only
    split_ifs
    · exact ⟨zero_lt_one, zero_lt_one⟩
    · exact ⟨hnext, abs_pos.mpr hl0⟩

theorem loop_invariant (p : Polynomial ℝ) (hp : p ≠ 0) (k : ℕ)
    (hk : k+1 ≤ p.natDegree) :
    Inv p k ((List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)) := by
  induction k with
  | zero => simpa using initial_inv p hp (by omega)
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact step_inv p k (by omega) _ (ih (by omega))

end Proofs
end RouthHurwitz.FractionFree
