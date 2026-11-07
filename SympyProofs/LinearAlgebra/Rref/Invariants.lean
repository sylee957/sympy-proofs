module

public import SympyProofs.LinearAlgebra.Rref.Algorithm
public import SympyProofs.LinearAlgebra.Rref.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

/-! Mathematical invariants for Gauss–Jordan elimination.
Structural properties are proved over a commutative ring; cancellation is scoped
to integral domains and pivot normalization to fields. The completed invariant
also supplies an abstract RREF certificate. -/

@[expose] public section

namespace SympyProofs.Rref

variable {R : Type*} {m n : ℕ}

namespace RrefAlgorithm

private theorem get_swap {α : Type*} (v : Vector α m) (p r i : Fin m) :
    (v.swap p.val r.val)[i.val] = v[(Equiv.swap p r i).val] := by
  by_cases hip : i = p
  · subst i
    simp
  by_cases hir : i = r
  · subst i
    simp
  · simp [Equiv.swap_apply_of_ne_of_ne hip hir,
      show i.val ≠ p.val from fun hh => hip (Fin.ext hh),
      show i.val ≠ r.val from fun hh => hir (Fin.ext hh)]

theorem set_pivot_get (pivots : Vector (Option (Fin n)) m) (c : Fin n) (r i : Fin m) :
    (pivots.set r.val (some c))[i.val] = if i = r then some c else pivots[i.val] := by
  simp [Vector.getElem_set, Fin.ext_iff, eq_comm]

section CommRing

variable [CommRing R]

/-- Entrywise mathematical description used by the elimination-loop invariant. -/
def crossRows (rows : Vector (Vector R n) m) (c : Fin n) (r : Fin m) :
    Vector (Vector R n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if i = r then rows[i.val][j.val]
    else rows[r.val][c.val] * rows[i.val][j.val] - rows[i.val][c.val] * rows[r.val][j.val]

theorem crossRows_get (rows : Vector (Vector R n) m) (c : Fin n) (r i : Fin m) (j : Fin n) :
    (crossRows rows c r)[i.val][j.val] =
      if i = r then rows[i.val][j.val]
      else rows[r.val][c.val] * rows[i.val][j.val] -
        rows[i.val][c.val] * rows[r.val][j.val] := by
  simp [crossRows]

theorem crossRows_self (rows : Vector (Vector R n) m) (c : Fin n) (r : Fin m) (j : Fin n) :
    (crossRows rows c r)[r.val][j.val] = rows[r.val][j.val] := by
  simp [crossRows_get]

theorem crossRows_zero {rows : Vector (Vector R n) m} {c : Fin n} {r i : Fin m} {j : Fin n}
    (hi : rows[i.val][j.val] = 0) (hr : rows[r.val][j.val] = 0) :
    (crossRows rows c r)[i.val][j.val] = 0 := by
  simp [crossRows_get, hi, hr]

theorem crossRows_column {rows : Vector (Vector R n) m} {c : Fin n} {r i : Fin m}
    (hi : i ≠ r) : (crossRows rows c r)[i.val][c.val] = 0 := by
  by_cases hz : rows[i.val][c.val] = 0 <;> simp [crossRows_get, hi, hz, mul_comm]

theorem crossRows_mulVec (rows : Vector (Vector R n) m) (c : Fin n) (r i : Fin m) (x : Fin n → R) :
    (toMatrix (crossRows rows c r)).mulVec x i =
      if i = r then (toMatrix rows).mulVec x i
      else rows[r.val][c.val] * (toMatrix rows).mulVec x i -
        rows[i.val][c.val] * (toMatrix rows).mulVec x r := by
  simp only [Matrix.mulVec, dotProduct, toMatrix, crossRows_get]
  split_ifs
  · rfl
  · simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- The processed columns are `[0, c)`. Used rows have isolated nonzero pivots;
unused rows vanish in every processed column. -/
structure Invariant (A : Matrix (Fin m) (Fin n) R) (rows : Vector (Vector R n) m)
    (pivots : Vector (Option (Fin n)) m) (c : ℕ) : Prop where
  known : ∀ (i : Fin m) (p : Fin n), pivots[i.val] = some p → p.val < c
  nonzero : ∀ (i : Fin m) (p : Fin n), pivots[i.val] = some p → rows[i.val][p.val] ≠ 0
  before : ∀ (i : Fin m) (p : Fin n), pivots[i.val] = some p → ∀ j < p, rows[i.val][j.val] = 0
  isolated : ∀ (i : Fin m) (p : Fin n), pivots[i.val] = some p → ∀ k ≠ i, rows[k.val][p.val] = 0
  unused : ∀ i : Fin m, pivots[i.val] = none → ∀ j : Fin n, j.val < c → rows[i.val][j.val] = 0
  kernel : ∀ x, A.mulVec x = 0 ↔ (toMatrix rows).mulVec x = 0

theorem Invariant.pivot_injective {A : Matrix (Fin m) (Fin n) R} {rows : Vector (Vector R n) m}
    {pivots : Vector (Option (Fin n)) m}
    {c : ℕ} (h : Invariant A rows pivots c) {i k : Fin m} {p : Fin n}
    (hi : pivots[i.val] = some p) (hk : pivots[k.val] = some p) : i = k := by
  by_contra hne
  exact h.nonzero i p hi (h.isolated k p hk i hne)

/-- Reindexing unused rows does not change the recorded pivots. -/
theorem Invariant.permute {A : Matrix (Fin m) (Fin n) R}
    {rows after : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m} {c : ℕ}
    (h : Invariant A rows pivots c) (e : Equiv.Perm (Fin m))
    (hrow : ∀ i : Fin m, after[i.val] = rows[(e i).val])
    (hpiv : ∀ i : Fin m, pivots[(e i).val] = pivots[i.val]) :
    Invariant A after pivots c := by
  refine ⟨h.known, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hi
    rw [hrow]
    exact h.nonzero (e i) p (by rwa [hpiv])
  · intro i p hi j hj
    rw [hrow]
    exact h.before (e i) p (by rwa [hpiv]) j hj
  · intro i p hi k hki
    rw [hrow]
    exact h.isolated (e i) p (by rwa [hpiv]) (e k) (fun hh => hki (e.injective hh))
  · intro i hi j hj
    rw [hrow]
    exact h.unused (e i) (by rwa [hpiv]) j hj
  · intro x
    rw [h.kernel]
    have hv (i : Fin m) : (toMatrix after).mulVec x i = (toMatrix rows).mulVec x (e i) := by
      simp [Matrix.mulVec, dotProduct, toMatrix, hrow]
    constructor
    · intro hx
      ext i
      simp [hv, hx]
    · intro hx
      ext i
      simpa [hv] using congrFun hx (e.symm i)

/-- Swapping two unused row slots preserves the elimination invariant. -/
theorem Invariant.swap_unused {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    {c : ℕ} (h : Invariant A rows pivots c)
    (p r : Fin m) (hp : pivots[p.val] = none) (hr : pivots[r.val] = none) :
    Invariant A (rows.swap p.val r.val) pivots c := by
  let e := Equiv.swap p r
  have hrow (i : Fin m) : (rows.swap p.val r.val)[i.val] = rows[(e i).val] := get_swap rows p r i
  have hpiv (i : Fin m) : pivots[(e i).val] = pivots[i.val] := by
    by_cases hip : i = p
    · subst i
      simp [e, hp, hr]
    by_cases hir : i = r
    · subst i
      simp [e, hp, hr]
    · simp [e, Equiv.swap_apply_of_ne_of_ne hip hir]
  exact h.permute e hrow hpiv

/-- Dense RREF has unit pivots in increasing columns and consecutive occupied rows. -/
structure DenseInvariant (A : Matrix (Fin m) (Fin n) R)
    (rows : Vector (Vector R n) m) (pivots : Vector (Option (Fin n)) m)
    (c rank : ℕ) : Prop extends Invariant A rows pivots c where
  rank_le : rank ≤ m
  unused_iff : ∀ i : Fin m, pivots[i.val] = none ↔ rank ≤ i.val
  monic : ∀ (i : Fin m) (p : Fin n), pivots[i.val] = some p → rows[i.val][p.val] = 1
  ordered : ∀ (i k : Fin m) (p q : Fin n), i < k →
    pivots[i.val] = some p → pivots[k.val] = some q → p < q

/-- At completion, the stored pivots are exactly Mathlib's leading entries. -/
theorem Invariant.isLeadingEntry_iff {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    (h : Invariant A rows pivots n) (i : Fin m) (p : Fin n) :
    (toMatrix rows).IsLeadingEntry i p ↔ pivots[i.val] = some p := by
  constructor
  · intro hp
    cases hi : pivots[i.val] with
    | none => exact (hp.2 (h.unused i hi p p.isLt)).elim
    | some q =>
      have hq : (toMatrix rows).IsLeadingEntry i q :=
        ⟨h.before i q hi, h.nonzero i q hi⟩
      exact congrArg some (hq.unique hp)
  · intro hp
    exact ⟨h.before i p hp, h.nonzero i p hp⟩

/-- The completed dense invariant implies Mathlib's row echelon condition. -/
theorem DenseInvariant.isRowEchelon {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    {rank : ℕ} (h : DenseInvariant A rows pivots n rank) :
    (toMatrix rows).IsRowEchelon := by
  intro i k hik j hz
  cases hk : pivots[k.val] with
  | none => exact h.unused k hk j j.isLt
  | some q =>
    cases hi : pivots[i.val] with
    | none =>
      have hri := (h.unused_iff i).mp hi
      have hkn := (h.unused_iff k).mpr (by omega)
      simp [hk] at hkn
    | some p =>
      have hpq := h.ordered i k p q hik hi hk
      have hjp : j ≤ p := le_of_not_gt fun hpj => h.nonzero i p hi (hz p hpj)
      exact h.before k q hk j (lt_of_le_of_lt hjp hpq)

/-- The completed dense invariant gives Mathlib's reduced row echelon form. -/
theorem DenseInvariant.isReducedRowEchelon {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    {rank : ℕ} (h : DenseInvariant A rows pivots n rank) :
    (toMatrix rows).IsReducedRowEchelon := by
  refine ⟨h.isRowEchelon, ?_, ?_⟩
  · intro i p hp
    exact h.monic i p ((h.toInvariant.isLeadingEntry_iff i p).mp hp)
  · intro i k p hik hp
    exact h.isolated k p ((h.toInvariant.isLeadingEntry_iff k p).mp hp) i (ne_of_lt hik)

theorem DenseInvariant.complete {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    {c rank : ℕ} (h : DenseInvariant A rows pivots c rank)
    (hrank : m ≤ rank) : DenseInvariant A rows pivots n rank := by
  refine { h with known := fun _ p _ => p.isLt, unused := ?_ }
  intro i hi
  have := (h.unused_iff i).mp hi
  omega

theorem DenseInvariant.swap_unused {A : Matrix (Fin m) (Fin n) R}
    {rows : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m}
    {c rank : ℕ} (h : DenseInvariant A rows pivots c rank)
    (p r : Fin m) (hp : pivots[p.val] = none) (hr : pivots[r.val] = none) :
    DenseInvariant A (rows.swap p.val r.val) pivots c rank := by
  refine ⟨h.toInvariant.swap_unused p r hp hr, h.rank_le, h.unused_iff, ?_, h.ordered⟩
  intro i q hi
  have hip : i ≠ p := by intro he; subst i; simp [hp] at hi
  have hir : i ≠ r := by intro he; subst i; simp [hr] at hi
  rw [get_swap]
  simpa only [Equiv.swap_apply_of_ne_of_ne hip hir] using h.monic i q hi

section Domain

variable [IsDomain R]

theorem crossRows_nonzero {rows : Vector (Vector R n) m} {c : Fin n} {r i : Fin m} {j : Fin n}
    (hp : rows[r.val][c.val] ≠ 0) (hi : rows[i.val][j.val] ≠ 0)
    (hr : rows[r.val][j.val] = 0) : (crossRows rows c r)[i.val][j.val] ≠ 0 := by
  rw [crossRows_get]
  split_ifs
  · exact hi
  · simpa [hr] using mul_ne_zero hp hi

theorem crossRows_kernel {rows : Vector (Vector R n) m} {c : Fin n} {r : Fin m}
    (hp : rows[r.val][c.val] ≠ 0) (x : Fin n → R) :
    (toMatrix rows).mulVec x = 0 ↔ (toMatrix (crossRows rows c r)).mulVec x = 0 := by
  constructor
  · intro hx
    ext i
    simp [crossRows_mulVec, hx]
  · intro hx
    have hr : (toMatrix rows).mulVec x r = 0 := by
      simpa [crossRows_mulVec] using congrFun hx r
    ext i
    have hi := congrFun hx i
    rw [crossRows_mulVec] at hi
    split_ifs at hi
    · exact hi
    · simpa [hr, hp] using hi

theorem crossRows_invariant {A : Matrix (Fin m) (Fin n) R} {rows : Vector (Vector R n) m}
    {pivots : Vector (Option (Fin n)) m}
    {c : Fin n} (h : Invariant A rows pivots c.val) {r : Fin m}
    (hr : pivots[r.val] = none) (hp : rows[r.val][c.val] ≠ 0) :
    Invariant A (crossRows rows c r) (pivots.set r.val (some c)) (c.val + 1) := by
  have hbefore (j : Fin n) (hj : j < c) : rows[r.val][j.val] = 0 :=
    h.unused r hr j hj
  constructor
  · intro i p hi
    rw [set_pivot_get] at hi
    split_ifs at hi with hir
    · cases hi
      omega
    · exact Nat.lt_succ_of_lt (h.known i p hi)
  · intro i p hi
    rw [set_pivot_get] at hi
    split_ifs at hi with hir
    · cases hi
      simpa [hir, crossRows_self] using hp
    · exact crossRows_nonzero hp (h.nonzero i p hi) (hbefore p (h.known i p hi))
  · intro i p hi j hj
    rw [set_pivot_get] at hi
    split_ifs at hi with hir
    · cases hi
      simpa [hir, crossRows_self] using hbefore j hj
    · exact crossRows_zero (h.before i p hi j hj) (hbefore j (lt_trans hj (h.known i p hi)))
  · intro i p hi k hki
    rw [set_pivot_get] at hi
    split_ifs at hi with hir
    · cases hi
      exact crossRows_column (hir ▸ hki)
    · exact crossRows_zero (h.isolated i p hi k hki) (hbefore p (h.known i p hi))
  · intro i hi j hj
    rw [set_pivot_get] at hi
    have hir : i ≠ r := by intro he; simp [he] at hi
    have hi' : pivots[i.val] = none := by simpa [hir] using hi
    by_cases hjc : j = c
    · subst j
      exact crossRows_column hir
    · have hjlt : j.val < c.val := by
        have : j.val ≠ c.val := fun he => hjc (Fin.ext he)
        omega
      exact crossRows_zero (h.unused i hi' j hjlt) (hbefore j hjlt)
  · intro x
    exact (h.kernel x).trans (crossRows_kernel hp x)

theorem Invariant.rescale {A : Matrix (Fin m) (Fin n) R}
    {rows after : Vector (Vector R n) m} {pivots : Vector (Option (Fin n)) m} {c : ℕ}
    (h : Invariant A rows pivots c) (d : Fin m → R) (hd : ∀ i, d i ≠ 0)
    (he : ∀ (i : Fin m) (j : Fin n), d i * after[i.val][j.val] = rows[i.val][j.val]) :
    Invariant A after pivots c := by
  have hz (i : Fin m) (j : Fin n) : after[i.val][j.val] = 0 ↔ rows[i.val][j.val] = 0 := by
    rw [← he i j, mul_eq_zero]
    simp [hd i]
  refine ⟨h.known, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hip
    exact fun he => h.nonzero i p hip ((hz i p).mp he)
  · intro i p hip j hj
    exact (hz i j).mpr (h.before i p hip j hj)
  · intro i p hip k hki
    exact (hz k p).mpr (h.isolated i p hip k hki)
  · intro i hi j hj
    exact (hz i j).mpr (h.unused i hi j hj)
  · intro x
    rw [h.kernel]
    have heq (i : Fin m) : d i * (toMatrix after).mulVec x i = (toMatrix rows).mulVec x i := by
      simp only [Matrix.mulVec, dotProduct, toMatrix, Finset.mul_sum, ← mul_assoc, he]
    constructor
    · intro hx
      ext i
      exact (mul_eq_zero.mp (by rw [heq i, hx]; rfl)).resolve_left (hd i)
    · intro hx
      ext i
      rw [← heq i, hx]
      simp

end Domain

end CommRing

section Field

variable {F : Type*} [Field F]

/-- Mathematical description of pivot-row normalization, used only in the proof. -/
def normalizedPivot (rows : Vector (Vector F n) m) (c : Fin n) (p : Fin m) : Vector F n :=
  Vector.ofFn fun j => rows[p.val][j.val] / rows[p.val][c.val]

def normalizedRows (rows : Vector (Vector F n) m) (c : Fin n) (p : Fin m) :
    Vector (Vector F n) m := rows.set p.val (normalizedPivot rows c p)

theorem normalizedRows_get (rows : Vector (Vector F n) m) (c : Fin n) (p i : Fin m) (j : Fin n) :
    (normalizedRows rows c p)[i.val][j.val] =
      if i = p then rows[i.val][j.val] / rows[p.val][c.val] else rows[i.val][j.val] := by
  by_cases hi : i = p
  · subst i
    simp [normalizedRows, normalizedPivot]
  · simp [normalizedRows, hi,
      show p.val ≠ i.val from fun he => hi (Fin.ext he.symm)]

theorem Invariant.normalize {A : Matrix (Fin m) (Fin n) F}
    {rows : Vector (Vector F n) m} {pivots : Vector (Option (Fin n)) m}
    {processed : ℕ} (h : Invariant A rows pivots processed) (c : Fin n) (p : Fin m)
    (hp : rows[p.val][c.val] ≠ 0) : Invariant A (normalizedRows rows c p) pivots processed := by
  apply h.rescale (fun i => if i = p then rows[p.val][c.val] else 1)
  · intro i
    split_ifs <;> simp_all
  · intro i j
    by_cases hi : i = p
    · subst i
      simp [normalizedRows_get, div_eq_mul_inv, mul_left_comm, hp]
    · simp [normalizedRows_get, hi]

/-- Normalizing the pivot and clearing its column preserves dense monic RREF. -/
theorem DenseInvariant.advance {A : Matrix (Fin m) (Fin n) F}
    {rows : Vector (Vector F n) m} {pivots : Vector (Option (Fin n)) m}
    {c : Fin n} {rank : ℕ} (h : DenseInvariant A rows pivots c.val rank)
    (p : Fin m) (hp : p.val = rank) (ha : rows[p.val][c.val] ≠ 0) :
    DenseInvariant A (crossRows (normalizedRows rows c p) c p)
      (pivots.set p.val (some c)) (c.val + 1) (rank + 1) := by
  have hpn : pivots[p.val] = none := (h.unused_iff p).mpr (by omega)
  have hn := h.toInvariant.normalize c p ha
  have hc := crossRows_invariant hn hpn (by simp [normalizedRows_get, ha])
  refine ⟨hc, by omega, ?_, ?_, ?_⟩
  · intro i
    rw [set_pivot_get]
    by_cases hi : i = p
    · subst i
      simp [hp]
    · have hne : i.val ≠ p.val := fun hv => hi (Fin.ext hv)
      simp only [ite_eq_right hi, h.unused_iff]
      omega
  · intro i q hi
    rw [set_pivot_get] at hi
    split_ifs at hi with hip
    · cases hi
      simp [crossRows_get, hip, normalizedRows_get, ha]
    · simp [crossRows_get, hip, normalizedRows_get, ha, h.monic i q hi,
        h.unused p hpn q (h.known i q hi)]
  · intro i k q t hik hi hk
    rw [set_pivot_get] at hi hk
    by_cases hip : i = p
    · subst i
      simp only [ite_true, Option.some.injEq] at hi
      subst q
      have hkp : k ≠ p := ne_of_gt hik
      have hkn : pivots[k.val] = none := (h.unused_iff k).mpr (by simp only [Fin.lt_def] at hik; omega)
      simp [hkp, hkn] at hk
    · by_cases hkp : k = p
      · subst k
        simp only [ite_true, Option.some.injEq] at hk
        subst t
        exact h.known i q (by simpa [hip] using hi)
      · exact h.ordered i k q t hik (by simpa [hip] using hi) (by simpa [hkp] using hk)

end Field

end RrefAlgorithm

/-- A mathematical certificate view of the two buffers. The executable algorithms
never construct this compact view. -/
def RrefAlgorithm.certificate
    (rows : Vector (Vector R n) m) (pivots : Vector (Option (Fin n)) m) : RrefResult R m n where
  rows := ((List.finRange m).filterMap fun i => pivots[i.val].map (·, rows[i.val])).toArray
  size_le := by
    simpa using (List.length_filterMap_le
      (fun i : Fin m => pivots[i.val].map (·, rows[i.val])) (List.finRange m))

@[simp] theorem RrefAlgorithm.mem_certificate
    (rows : Vector (Vector R n) m) (pivots : Vector (Option (Fin n)) m)
    (p : Fin n) (v : Vector R n) :
    (p, v) ∈ (certificate rows pivots).rows ↔
      ∃ i : Fin m, pivots[i.val] = some p ∧ rows[i.val] = v := by
  simp only [certificate, List.mem_toArray, List.mem_filterMap, List.mem_finRange,
    true_and, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨i, q, hi, rfl, hv⟩
    exact ⟨i, hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, p, hi, rfl, hv⟩

open RrefAlgorithm in
theorem RrefAlgorithm.Invariant.certificate_valid [CommRing R]
    {A : Matrix (Fin m) (Fin n) R} {rows : Vector (Vector R n) m}
    {pivots : Vector (Option (Fin n)) m} (h : Invariant A rows pivots n) :
    (certificate rows pivots).Valid A := by
  let out := certificate rows pivots
  have hmem := mem_certificate rows pivots
  constructor
  · change (out.rows.toList.map Prod.fst).Nodup
    change (((List.finRange m).filterMap
      (fun i => pivots[i.val].map (·, rows[i.val]))).map Prod.fst).Nodup
    rw [List.map_filterMap]
    have hf : (fun i : Fin m => (pivots[i.val].map (·, rows[i.val])).map Prod.fst) =
        (fun i : Fin m => pivots[i.val]) := by
      funext i
      simp [Function.comp_def]
    rw [hf]
    apply List.Nodup.filterMap ?_ (List.nodup_finRange m)
    intro i k p hi hk
    exact h.pivot_injective hi hk
  · intro p v hv
    obtain ⟨i, hi, rfl⟩ := (hmem p v).mp hv
    exact h.nonzero i p hi
  · intro p v hv j hj
    obtain ⟨i, hi, rfl⟩ := (hmem p v).mp hv
    exact h.before i p hi j hj
  · intro p v hv q hq hne
    obtain ⟨i, hi, rfl⟩ := (hmem p v).mp hv
    obtain ⟨w, hw⟩ := (out.mem_pivots_iff q).mp hq
    obtain ⟨k, hk, rfl⟩ := (hmem q w).mp hw
    have hik : i ≠ k := by
      intro he
      subst k
      exact hne (Option.some.inj (hk.symm.trans hi))
    exact h.isolated k q hk i hik
  · intro x
    rw [h.kernel x, out.matrix_mulVec_eq_zero_iff]
    constructor
    · intro hx p v hv
      obtain ⟨i, hi, rfl⟩ := (hmem p v).mp hv
      exact congrFun hx i
    · intro hx
      ext i
      cases hi : pivots[i.val] with
      | none =>
        simp [Matrix.mulVec, dotProduct, toMatrix, h.unused i hi]
      | some p =>
        exact hx p rows[i.val] ((hmem p _).mpr ⟨i, hi, rfl⟩)

end SympyProofs.Rref
