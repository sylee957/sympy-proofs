import SympyProofs.RouthHurwitz.FractionFree.Loop

/-! Degree bounds and nonzero divisors for `Exact.run`, independent of root counts.
These facts hold over any linearly ordered field, including ordered fraction
fields of polynomial coefficient rings. -/
namespace RouthHurwitz.FractionFree.Proofs
open Polynomial Imperative Imperative.Bounds
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure Shape (n k : ℕ) (s : Locals (K := K) n) : Prop where
  upper_nonzero : s.1[0]'(width_pos n) ≠ 0
  lower_nonzero : s.2.1[0]'(width_pos n) ≠ 0
  upper_support : ∀ j, n < k + 2*j → rowFunction s.1 j = 0
  lower_support : ∀ j, n < k+1 + 2*j → rowFunction s.2.1 j = 0
  divisor_pos : 0 < s.2.2.2.2.2.1
  nextDivisor_pos : 0 < s.2.2.2.2.2.2

private theorem initial_shape (p : Polynomial K) (hp : p ≠ 0) (hn : 0 < p.natDegree) :
    Shape p.natDegree 0 (initialLocals p) := by
  let n := p.natDegree
  let upper := initial p 0
  let raw := initial p 1
  let w : Fin (width n+1) := ⟨width n, Nat.lt_succ_self _⟩
  let lower : Vector K (width n) := (repair n w upper raw).1
  have hr : ∀ j, n-1 < 2*j → rowFunction raw j = 0 := by
    rw [show raw = initial p 1 from rfl, rowFunction_initial]
    intro j hj
    simp [initialRow, show ¬ 2*j+1 ≤ p.natDegree by dsimp [n] at hj; omega]
  have hu0 : upper[0]'(width_pos n) ≠ 0 := by
    have h := leadingCoeff_ne_zero.mpr hp
    change p.coeff p.natDegree ≠ 0 at h
    simpa only [upper, initial, initialCoefficients, Vector.getElem_ofFn, Nat.mul_zero, Nat.add_zero,
      Nat.zero_le, if_true, Nat.sub_zero] using h
  have hu : rowFunction upper 0 ≠ 0 := by simpa [rowFunction, width_pos] using hu0
  have he := repair_function n n w upper raw (by omega) hr
  have hl := repairRow_pivot_ne_zero_of_previous n w (rowFunction upper) (rowFunction raw) (ne_of_gt hn) hu
  have hl0 : lower[0]'(width_pos n) ≠ 0 := by
    change rowFunction lower = _ at he
    have h := congrFun he 0
    simp only [rowFunction, dif_pos (width_pos n)] at h
    exact h ▸ hl
  change Shape n 0 (upper, lower, [upper, lower], _, _, 1, 1)
  refine ⟨hu0, hl0, ?_, ?_, zero_lt_one, zero_lt_one⟩
  · intro j hj
    change rowFunction (initial p 0) j = 0
    rw [rowFunction_initial]
    simp [initialRow, show ¬ 2*j ≤ p.natDegree by dsimp [n] at hj; omega]
  · intro j hj
    change rowFunction lower j = 0
    rw [show rowFunction lower = _ from he]
    exact repairRow_support n w _ _ hr j (by omega)

 theorem Shape.advance (n k : ℕ) (hk : k+2 ≤ n) (s : Locals (K := K) n)
    (h : Shape n k s) : Shape n (k+1) (step n k s) := by
  obtain ⟨upper, lower, rows, count, deg, d, e⟩ := s
  obtain ⟨hu0, hl0, hu, hl, hd, he⟩ := h
  dsimp only at hu0 hl0 hu hl hd he
  let w : Fin (width n+1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (if lower[0]'(width_pos _) < 0 then (-1 : K) else 1) *
        (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
          upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj)) / d
    else 0)
  let row : Vector K (width n) := (repair (n+1-(k+2)) w lower raw).1
  have hr : ∀ j, n-(k+2) < 2*j → rowFunction raw j = 0 := by
    intro j hj
    by_cases hactive : j < activeWidth n (k+2)
    · have hj' := next_index_lt n k j hactive
      have hh : j < width n := by omega
      have huz := hu (j+1) (by omega)
      have hlz := hl (j+1) (by omega)
      simp only [rowFunction, dif_pos hj'] at huz hlz
      simp [rowFunction, raw, w, hh, hactive, huz, hlz]
    · simp only [rowFunction, raw, Vector.getElem_ofFn]
      split_ifs <;> simp_all
  have hdeg : n+1-(k+2)-1 = n-(k+2) := by omega
  have hrow := repair_function n (n+1-(k+2)) w lower raw (by omega) (by rw [hdeg]; exact hr)
  have hp := repairRow_pivot_ne_zero_of_previous (n+1-(k+2)) w
    (rowFunction lower) (rowFunction raw) (by omega)
    (by simpa [rowFunction, width_pos] using hl0)
  have hrow0 : row[0]'(width_pos n) ≠ 0 := by
    change rowFunction row = _ at hrow
    have hh := congrFun hrow 0
    simp only [rowFunction, dif_pos (width_pos n)] at hh
    exact hh ▸ hp
  change Shape n (k+1) (lower, row, List.append rows [row], _, _,
    (if raw[0]'(width_pos n) = 0 then 1 else e),
    (if raw[0]'(width_pos n) = 0 then 1 else |lower[0]'(width_pos n)|))
  refine ⟨hl0, hrow0, hl, ?_, ?_, ?_⟩
  · intro j hj
    change rowFunction row j = 0
    rw [show rowFunction row = _ from hrow]
    apply repairRow_support _ _ _ _ (by rw [hdeg]; exact hr) j
    omega
  · dsimp only
    split_ifs <;> positivity
  · dsimp only
    split_ifs
    · exact zero_lt_one
    · exact abs_pos.mpr hl0

 theorem loop_shape (p : Polynomial K) (hp : p ≠ 0) (k : ℕ) (hk : k+1 ≤ p.natDegree) :
    Shape p.natDegree k
      ((List.range k).foldl (fun s j => step p.natDegree j s) (initialLocals p)) := by
  induction k with
  | zero => simpa using initial_shape p hp (by omega)
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact Shape.advance _ k (by omega) _ (ih (by omega))

end RouthHurwitz.FractionFree.Proofs
