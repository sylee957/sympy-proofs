import SympyProofs.RouthHurwitz.FractionFree.AlgebraicInvariant
import SympyProofs.RouthHurwitz.FractionFree.Determinants

/-! Exact cancellation over coefficient rings, through regular steps and both repairs. -/
namespace RouthHurwitz.FractionFree
open Polynomial Imperative Imperative.Bounds Proofs

open Arithmetic

variable {R K : Type*} [CommRing R] [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]
variable (f : R →+* K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem mapped_rowFunction {W : ℕ} (row : Vector K W) :
    MappedRow f (rowFunction row) ↔ ∀ j (hj : j < W), ∃ z : R, row[j] = f z := by
  constructor
  · intro h j hj
    simpa [rowFunction, hj] using h j
  · intro h j
    by_cases hj : j < W
    · simpa [rowFunction, hj] using h j hj
    · exact ⟨0, by simp [rowFunction, hj]⟩

omit [IsStrictOrderedRing K] in
private theorem mapped_repair {W : ℕ} (d : ℕ) (w : Fin (W+2))
    (upper raw : Vector K (W+1)) (hu : MappedRow f (rowFunction upper))
    (hr : MappedRow f (rowFunction raw)) : MappedRow f (rowFunction (repair d w upper raw).1) := by
  apply (mapped_rowFunction f _).mpr
  have hu := (mapped_rowFunction f upper).mp hu
  have hr := (mapped_rowFunction f raw).mp hr
  intro j hj
  simp only [repair]
  split_ifs
  all_goals simp only [Id.run_pure]
  · simp only [Vector.getElem_ofFn]
    split_ifs with hs
    · obtain ⟨a, ha⟩ := hr j hj
      obtain ⟨b, hb⟩ := hr (j + scan w raw) (by omega)
      exact ⟨a + (-1)^scan w raw * b, by simp [ha, hb]⟩
    · exact hr j hj
  · exact hr j hj
  · simp only [Vector.getElem_ofFn]
    obtain ⟨a, ha⟩ := hu j hj
    exact ⟨a * ((d - 2*j : ℕ) : R), by simp [ha]⟩

omit [IsStrictOrderedRing K] in
private theorem repair_of_pivot {W : ℕ} (d : ℕ) (w : Fin (W+2))
    (upper raw : Vector K (W+1)) (hw : 0 < w.val) (hr : raw[0] ≠ 0) :
    (repair d w upper raw).1 = raw := by
  have hn : (nonzeroIndices w (rowFunction raw)).Nonempty :=
    ⟨0, by simp [nonzeroIndices, rowFunction, hw, hr]⟩
  rw [repair_eq]
  simp only [repairRow, if_pos hn, rowFunction, dif_pos (Nat.zero_lt_succ W), if_neg hr]
  apply Vector.ext
  intro j hj
  simp only [tabulate, Vector.getElem_ofFn, rowFunction, dif_pos hj]

omit [IsStrictOrderedRing K] in
private theorem raw_function (n k : ℕ) (upper lower : Vector K (width n))
    (d : K) (ht : ∀ j, activeWidth n (k+2) ≤ j →
      rowFunction upper (j+1) = 0 ∧ rowFunction lower (j+1) = 0) :
    rowFunction (Vector.ofFn (fun j : Fin (width n) =>
      if hj : j.val < activeWidth n (k + 2) then
        (if lower[0]'(width_pos _) < 0 then (-1 : K) else 1) *
          (lower[0]'(width_pos _) * upper[j.val + 1]'(next_index_lt n k j.val hj) -
            upper[0]'(width_pos _) * lower[j.val + 1]'(next_index_lt n k j.val hj)) / d
      else 0)) = fun j =>
        (if lower[0]'(width_pos _) < 0 then (-1 : K) else 1) *
          (lower[0]'(width_pos _) * rowFunction upper (j+1) -
            upper[0]'(width_pos _) * rowFunction lower (j+1)) / d := by
  funext j
  by_cases hj : j < activeWidth n (k+2)
  · have hj' := next_index_lt n k j hj
    simp [rowFunction, hj, show j < width n by omega, hj']
  · obtain ⟨hu, hl⟩ := ht j (by omega)
    rw [hu, hl]
    simp only [mul_zero, sub_zero, zero_div]
    unfold rowFunction
    split_ifs <;> simp [hj]

/-- The signed numerator of an active cell in the actual inline loop.
This proof-only expression uses the same bounded indexing as `Exact.run`. -/
def cellNumerator (n k : ℕ) (s : Locals (K := K) n)
    (j : Fin (activeWidth n (k+2))) : K :=
  (if s.2.1[0]'(width_pos n) < 0 then (-1 : K) else 1) *
    (s.2.1[0]'(width_pos n) * s.1[j.val+1]'(next_index_lt n k j.val j.isLt) -
      s.1[0]'(width_pos n) * s.2.1[j.val+1]'(next_index_lt n k j.val j.isLt))

/-- Every active numerator is its nonzero loop divisor times a coefficient-ring value. -/
def ExactDivision (n k : ℕ) (s : Locals (K := K) n) : Prop :=
  s.2.2.2.2.2.1 ≠ 0 ∧ (∃ d : R, f d = s.2.2.2.2.2.1) ∧
    ∀ j, ∃ q : R, cellNumerator n k s j = s.2.2.2.2.2.1 * f q

/-- The arithmetic invariant for the current uninterrupted segment. The
segment's seed rows and index exist only in the proof. -/
private def Segment (n : ℕ) (s : Locals (K := K) n) : Prop :=
  ∃ u l : ℕ → K, ∃ k : ℕ,
    MappedRow f u ∧ MappedRow f l ∧ Regular u l k ∧
    rowFunction s.1 = (fun j => s.2.2.2.2.2.1 * (pair u l k).1 j) ∧
    rowFunction s.2.1 = (fun j => s.2.2.2.2.2.2 * (pair u l k).2 j) ∧
    s.2.2.2.2.2.2 = |weight u l k| ∧
    (∃ d : R, f d = s.2.2.2.2.2.1) ∧ (∃ e : R, f e = s.2.2.2.2.2.2)

private theorem bareiss_scaled (u l : ℕ → K) (d e : K) (hd : d ≠ 0) (hl : l 0 ≠ 0)
    (j : ℕ) :
    (if e*l 0 < 0 then (-1 : K) else 1) *
      (e*l 0 * (d*u (j+1)) - d*u 0 * (e*l (j+1))) / d =
      |e*l 0| * Arithmetic.next u l j := by
  unfold Arithmetic.next
  split_ifs with h
  · rw [abs_of_neg h]
    field_simp
  · rw [abs_of_nonneg (le_of_not_gt h)]
    field_simp

private theorem step_segment (p : Polynomial K)
    (k : ℕ) (hk : k+2 ≤ p.natDegree) (s : Locals (K := K) p.natDegree) (hi : Shape p.natDegree k s)
    (hs : Segment f p.natDegree s) :
    Segment f p.natDegree (step p.natDegree k s) ∧
      MappedRow f (rowFunction (step p.natDegree k s).2.1) ∧ ExactDivision f p.natDegree k s := by
  let n := p.natDegree
  obtain ⟨upper, lower, rows, count, deg, d, e⟩ := s
  obtain ⟨hu0, hl0, hu, hl, hd, hepos⟩ := hi
  dsimp only at hu0 hl0 hu hl hd hepos
  obtain ⟨u, l, t, hui, hli, hreg, hue, hle, he, hdmap, hemap⟩ := hs
  dsimp only at hue hle he hdmap hemap
  let w : Fin (width n + 1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (if lower[0]'(width_pos _) < 0 then (-1 : K) else 1) *
        (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
          upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj)) / d
    else 0)
  have hu0 : upper[0]'(width_pos _) = d * (pair u l t).1 0 := by
    simpa [rowFunction, width_pos] using congrFun hue 0
  have he0 : lower[0]'(width_pos _) = e * (pair u l t).2 0 := by
    simpa [rowFunction, width_pos] using congrFun hle 0
  have hcanon : (pair u l t).2 0 ≠ 0 := by
    intro h
    apply hl0
    simp [he0, h]
  have hreg' := (regular_step u l t).mpr ⟨hreg, hcanon⟩
  have habs : |lower[0]'(width_pos _)| = |weight u l (t+1)| := by
    rw [he0, he, weight_step, abs_mul, abs_mul, abs_abs]
  have htail : ∀ j, activeWidth n (k+2) ≤ j →
      rowFunction upper (j+1) = 0 ∧ rowFunction lower (j+1) = 0 := by
    intro j hj
    have hj1 : n < k + 2*(j+1) := by dsimp [activeWidth, width] at hj; omega
    have hj2 : n < k+1 + 2*(j+1) := by omega
    exact ⟨hu (j+1) hj1, hl (j+1) hj2⟩
  have hraw : rowFunction raw = fun j => |weight u l (t+1)| * (pair u l (t+1)).2 j := by
    have hf := raw_function n k upper lower d htail
    change rowFunction raw = _ at hf
    rw [hf]
    funext j
    simp only [hue, hle, hu0, he0, pair_step]
    rw [bareiss_scaled _ _ d e (ne_of_gt hd) hcanon j, ← he0, habs]
  have hrawi : MappedRow f (rowFunction raw) := by
    rw [hraw]
    exact mapped_abs_weighted_pair f u l hui hli (t+1) hreg'
  have hlint : MappedRow f (rowFunction lower) := by
    rw [hle, he]
    exact mapped_abs_weighted_pair f u l hui hli t hreg
  have hexact : ExactDivision f n k (upper, lower, rows, count, deg, d, e) := by
    refine ⟨ne_of_gt hd, hdmap, ?_⟩
    intro j
    obtain ⟨q, hq⟩ := hrawi j.val
    have hj : j.val < width n := by have := j.isLt; dsimp [activeWidth] at this; omega
    simp only [rowFunction, dif_pos hj, raw, Vector.getElem_ofFn, w, dif_pos j.isLt] at hq
    change cellNumerator n k (upper, lower, rows, count, deg, d, e) j / d = f q at hq
    refine ⟨q, ?_⟩
    have heq := (div_eq_iff (ne_of_gt hd)).mp hq
    simpa only [mul_comm] using heq
  have hrow := mapped_repair f (n+1-(k+2)) w lower raw hlint hrawi
  change Segment f n (lower, (repair (n+1-(k+2)) w lower raw).1,
    List.append rows [(repair (n+1-(k+2)) w lower raw).1],
    count + (if lower[0]'(width_pos _) * (repair (n+1-(k+2)) w lower raw).1[0] < 0 then 1 else 0),
    deg || !(repair (n+1-(k+2)) w lower raw).2,
    (if raw[0]'(width_pos _) = 0 then 1 else e),
    (if raw[0]'(width_pos _) = 0 then 1 else |lower[0]'(width_pos _)|)) ∧ _
  refine ⟨?_, hrow, hexact⟩
  by_cases hz : raw[0]'(width_pos _) = 0
  · refine ⟨rowFunction lower, rowFunction (repair (n+1-(k+2)) w lower raw).1,
      0, hlint, hrow, trivial, ?_, ?_, ?_, ⟨1, by simp [hz]⟩, ⟨1, by simp [hz]⟩⟩ <;> simp [hz, pair, weight]
    all_goals rfl
  · have hw : 0 < w.val := by dsimp [w, activeWidth, width]; omega
    have hr := repair_of_pivot (n+1-(k+2)) w lower raw hw hz
    refine ⟨u, l, t+1, hui, hli, hreg', ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [if_neg hz, pair_step] using hle
    · simpa only [if_neg hz, hr, habs] using hraw
    · simpa only [if_neg hz] using habs
    · simpa only [if_neg hz] using hemap
    · obtain ⟨a, ha⟩ := hlint 0
      simp only [rowFunction, dif_pos (width_pos p.natDegree)] at ha
      dsimp only
      rw [if_neg hz]
      by_cases hneg : lower[0]'(width_pos n) < 0
      · exact ⟨-a, by rw [map_neg, ← ha, abs_of_neg hneg]⟩
      · exact ⟨a, by rw [← ha, abs_of_nonneg (le_of_not_gt hneg)]⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem mapped_initial (p : Polynomial K)
    (hc : ∀ j, ∃ z : R, p.coeff j = f z) (parity : ℕ) :
    MappedRow f (rowFunction (initial p parity)) := by
  rw [rowFunction_initial]
  intro j
  simp only [initialRow]
  split_ifs
  · exact hc _
  · exact ⟨0, by simp⟩

private theorem initial_segment (p : Polynomial K)
    (hc : ∀ j, ∃ z : R, p.coeff j = f z) :
    Segment f p.natDegree (initialLocals p) ∧
      ∀ row ∈ (initialLocals p).2.2.1, MappedRow f (rowFunction row) := by
  have hu := mapped_initial f p hc 0
  have hl := mapped_repair f p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩
    (initial p 0) (initial p 1) hu (mapped_initial f p hc 1)
  constructor
  · refine ⟨rowFunction (initial p 0),
      rowFunction (repair p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩
        (initial p 0) (initial p 1)).1, 0, hu, hl, trivial, ?_, ?_, ?_,
        ⟨1, by simp [initialLocals_eq]⟩, ⟨1, by simp [initialLocals_eq]⟩⟩
    all_goals simp [initialLocals_eq, pair, weight]
    all_goals rfl
  · intro row hr
    change row ∈ [initial p 0, (repair p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩
      (initial p 0) (initial p 1)).1] at hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst row; exact hu
    · have hr := List.mem_singleton.mp hr
      subst row
      exact hl

omit [IsStrictOrderedRing K] in
private theorem step_rows (n k : ℕ) (s : Locals (K := K) n) :
    (step n k s).2.2.1 = List.append s.2.2.1 [(step n k s).2.1] := by
  rfl

private theorem loop_mapped (p : Polynomial K) (hp : p ≠ 0)
    (hc : ∀ j, ∃ z : R, p.coeff j = f z) (k : ℕ) (hk : k+1 ≤ p.natDegree) :
    let s := (List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)
    Segment f p.natDegree s ∧ ∀ row ∈ s.2.2.1, MappedRow f (rowFunction row) := by
  induction k with
  | zero => simpa using initial_segment f p hc
  | succ k ih =>
    have ih := ih (by omega)
    have hi := loop_shape p hp k (by omega)
    have hs := step_segment f p k (by omega) _ hi ih.1
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨hs.1, ?_⟩
    intro row hr
    rw [step_rows] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ih.2 row hr
    · have hr := List.mem_singleton.mp hr
      subst row
      exact hs.2.1

/-- A coefficient ring is preserved by the entire runner, including both
repairs. No divisibility or regularity hypothesis is imposed on the input. -/
theorem run_preserves_ring (p : Polynomial K)
    (hc : ∀ j, ∃ z : R, p.coeff j = f z) :
    ∀ row ∈ (Exact.run p).rows, ∀ j (hj : j < width p.natDegree), ∃ z : R, row[j] = f z := by
  by_cases hn : p.natDegree = 0
  · intro row hr
    simp only [Exact.Proofs.run_eq, if_pos hn, List.mem_singleton] at hr
    subst row
    exact (mapped_rowFunction f _).mp (mapped_initial f p hc 0)
  · have hp : p ≠ 0 := by intro hz; subst p; simp at hn
    have hi := (loop_mapped f p hp hc (p.natDegree-1) (by omega)).2
    simp only [Exact.Proofs.run_eq, if_neg hn]
    change ∀ row ∈ ((List.range (p.natDegree-1)).foldl
      (fun s j => step p.natDegree j s) (initialLocals p)).2.2.1, _
    intro row hr
    exact (mapped_rowFunction f _).mp (hi row hr)

/-- Every division performed by `Exact.run` is exact over the coefficient ring,
including after either repair. The index identifies an iteration of its loop. -/
theorem run_exact_division (p : Polynomial K)
    (hc : ∀ j, ∃ a : R, p.coeff j = f a) (k : ℕ) (hk : k+2 ≤ p.natDegree) :
    let s := (List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)
    ExactDivision f p.natDegree k s := by
  have hp : p ≠ 0 := by intro hz; subst p; simp at hk
  exact (step_segment f p k hk _ (loop_shape p hp k (by omega))
    (loop_mapped f p hp hc k (by omega)).1).2.2

/-- For an injective coefficient-ring map, exactness gives genuine ring
 divisibility of each numerator by the delayed divisor, not just field equality. -/
theorem run_divisor_dvd_numerator (hf : Function.Injective f) (p : Polynomial K)
    (hc : ∀ j, ∃ a : R, p.coeff j = f a) (k : ℕ) (hk : k+2 ≤ p.natDegree) :
    let s := (List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)
    ∀ j, ∀ divisor numerator : R,
      f divisor = s.2.2.2.2.2.1 → f numerator = cellNumerator p.natDegree k s j →
      divisor ∣ numerator := by
  intro s j divisor numerator hd hn
  obtain ⟨q, hq⟩ := (run_exact_division f p hc k hk).2.2 j
  refine ⟨q, hf ?_⟩
  rw [map_mul, hd, hn]
  exact hq

end RouthHurwitz.FractionFree
