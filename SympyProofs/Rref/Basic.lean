module

public import Mathlib

/-! Pivot-indexed RREF certificates over a commutative ring.
Rows may be stored in any order, with their scale in the pivot entry. This module
contains storage operations and the validity contract. Interpretation in a
fraction field and uniqueness up to scaling are proved in `Rref.FractionField`. -/

@[expose] public section

namespace SympyProofs.Rref

/-- Nonzero reduced rows paired with their pivot columns. Zero rows are omitted;
array order is irrelevant. The pivot entry is the row's implicit scale. -/
structure RrefResult (R : Type*) (m n : ℕ) where
  rows : Array (Fin n × Vector R n)
  size_le : rows.size ≤ m

abbrev RrefOperation (R : Type*) :=
  {m n : ℕ} → Matrix (Fin m) (Fin n) R → RrefResult R m n

variable {R : Type*} {m n : ℕ}

/-- Pivot keys in storage order, used only to state distinctness. -/
def RrefResult.keys (r : RrefResult R m n) : List (Fin n) :=
  r.rows.toList.map Prod.fst

/-- The set of pivot columns is independent of storage order. -/
def RrefResult.pivots (r : RrefResult R m n) : Finset (Fin n) := r.keys.toFinset

/-- Look up a reduced row by its pivot, without sorting or moving any rows. -/
def RrefResult.lookup (r : RrefResult R m n) (p : Fin n) : Option (Vector R n) :=
  r.rows.findSome? fun e => if p == e.1 then some e.2 else none

theorem RrefResult.lookup_eq_list (r : RrefResult R m n) (p : Fin n) :
    r.lookup p = r.rows.toList.lookup p := by
  simp [lookup, List.lookup_eq_findSome?]

/-- Matrix of the stored equations, in their arbitrary storage order. -/
def RrefResult.matrix (r : RrefResult R m n) : Matrix (Fin r.rows.size) (Fin n) R :=
  fun i j => r.rows[i.val].2[j.val]

/-- Missing pivots represent zero rows. -/
def RrefResult.row [Zero R] (r : RrefResult R m n) (p j : Fin n) : R :=
  ((r.lookup p).getD (Vector.replicate n 0))[j.val]

private theorem lookup_of_mem {α β : Type*} [DecidableEq α]
    (l : List (α × β)) (hn : (l.map Prod.fst).Nodup)
    (p : α) (v : β) (hv : (p, v) ∈ l) : l.lookup p = some v := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hv with he | ht
    · subst a
      simp
    · have hp : p ≠ a.1 := by
        intro he
        apply hn.1
        exact List.mem_map.mpr ⟨(p, v), ht, he⟩
      rcases a with ⟨a, b⟩
      have hbeq : (p == a) = false := beq_eq_false_iff_ne.mpr hp
      rw [List.lookup_cons, hbeq]
      exact ih hn.2 ht

theorem RrefResult.lookup_none_iff (r : RrefResult R m n) (p : Fin n) :
    r.lookup p = none ↔ p ∉ r.pivots := by
  simp only [lookup_eq_list, List.lookup_eq_none_iff, bne_iff_ne]
  simp only [pivots, List.mem_toFinset, keys, List.mem_map, not_exists, not_and]
  constructor
  · intro h e he hep
    exact h e he hep.symm
  · intro h e he hpe
    exact h e he hpe.symm

theorem RrefResult.mem_pivots_iff (r : RrefResult R m n) (p : Fin n) :
    p ∈ r.pivots ↔ ∃ v, (p, v) ∈ r.rows := by
  simp [pivots, keys, List.mem_map, Prod.exists, eq_comm]

/-- Canonical pivot order is a view, never a constraint on the stored array. -/
def RrefResult.sortedPivots (r : RrefResult R m n) : List (Fin n) :=
  r.pivots.sort (· ≤ ·)

@[simp] theorem RrefResult.mem_sortedPivots (r : RrefResult R m n) (p : Fin n) :
    p ∈ r.sortedPivots ↔ p ∈ r.pivots := by simp [sortedPivots]

theorem RrefResult.sortedPivots_length_le (r : RrefResult R m n) :
    r.sortedPivots.length ≤ m := by
  calc
    r.sortedPivots.length = r.pivots.card := by simp [sortedPivots]
    _ ≤ r.keys.length := List.toFinset_card_le _
    _ = r.rows.size := by simp [keys]
    _ ≤ m := r.size_le

section CommRing

variable [CommRing R]

/-- The stored equations can be checked without assigning canonical row numbers. -/
theorem RrefResult.matrix_mulVec_eq_zero_iff (r : RrefResult R m n) (x : Fin n → R) :
    r.matrix.mulVec x = 0 ↔
      ∀ p v, (p, v) ∈ r.rows → ∑ j : Fin n, v[j.val] * x j = 0 := by
  constructor
  · intro hx p v hv
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hv
    simpa [matrix, Matrix.mulVec, dotProduct, he] using congrFun hx ⟨i, hi⟩
  · intro hx
    ext i
    exact hx r.rows[i.val].1 r.rows[i.val].2
      (Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩)

/-- All conditions are stated over a commutative ring. Pivot entries need only be
nonzero, not units, and no order of stored rows is prescribed. -/
structure RrefResult.Valid (A : Matrix (Fin m) (Fin n) R) (r : RrefResult R m n) : Prop where
  distinct : r.keys.Nodup
  pivot_ne_zero : ∀ p v, (p, v) ∈ r.rows → v[p.val] ≠ 0
  before_pivot : ∀ p v, (p, v) ∈ r.rows → ∀ j < p, v[j.val] = 0
  other_pivot : ∀ p v, (p, v) ∈ r.rows → ∀ q ∈ r.pivots, q ≠ p → v[q.val] = 0
  kernel_iff : ∀ x : Fin n → R, A.mulVec x = 0 ↔ r.matrix.mulVec x = 0

theorem RrefResult.lookup_of_mem {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (p : Fin n) (v : Vector R n)
    (hv : (p, v) ∈ r.rows) : r.lookup p = some v := by
  rw [lookup_eq_list]
  exact SympyProofs.Rref.lookup_of_mem _ hr.distinct p v (by simpa using hv)

theorem RrefResult.row_of_mem {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (p : Fin n) (v : Vector R n)
    (hv : (p, v) ∈ r.rows) (j : Fin n) : r.row p j = v[j.val] := by
  simp [row, r.lookup_of_mem hr p v hv]

theorem RrefResult.row_zero_of_not_pivot (r : RrefResult R m n)
    (p : Fin n) (hp : p ∉ r.pivots) (j : Fin n) : r.row p j = 0 := by
  simp [row, (r.lookup_none_iff p).mpr hp]

theorem RrefResult.pivot_ne_zero {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (p : Fin n) (hp : p ∈ r.pivots) :
    r.row p p ≠ 0 := by
  obtain ⟨v, hv⟩ := (r.mem_pivots_iff p).mp hp
  rw [r.row_of_mem hr p v hv]
  exact hr.pivot_ne_zero p v hv

theorem RrefResult.row_before_pivot {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (p : Fin n) (hp : p ∈ r.pivots)
    (j : Fin n) (hj : j < p) : r.row p j = 0 := by
  obtain ⟨v, hv⟩ := (r.mem_pivots_iff p).mp hp
  rw [r.row_of_mem hr p v hv]
  exact hr.before_pivot p v hv j hj

theorem RrefResult.row_other_pivot {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (p : Fin n) (hp : p ∈ r.pivots)
    (q : Fin n) (hq : q ∈ r.pivots) (hne : q ≠ p) : r.row p q = 0 := by
  obtain ⟨v, hv⟩ := (r.mem_pivots_iff p).mp hp
  rw [r.row_of_mem hr p v hv]
  exact hr.other_pivot p v hv q hq hne

/-- Equality of represented rows, expressed entirely in the coefficient ring.
The pivots match and rows with the same pivot agree by cross multiplication. -/
def RrefResult.Equivalent (r s : RrefResult R m n) : Prop :=
  r.pivots = s.pivots ∧ ∀ p j, s.row p p * r.row p j = r.row p p * s.row p j

end CommRing

end SympyProofs.Rref
