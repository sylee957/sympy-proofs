module

public import SympyProofs.Gosper.ShiftlessDecomposition.Algorithm

/-!
# Specification of shiftless decompositions

The coefficient field `K` has characteristic zero. An occurrence `(h, e)` of a base `p` represents
`p(X + h) ^ e`. Bases may be reducible. Integer translation, rather than
irreducibility, determines the separation required between groups.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

open Polynomial

variable {K : Type*} [Field K]

def shift (p : Polynomial K) (h : ℤ) : Polynomial K := taylor (h : K) p

def Group.expand (g : Group K) : Polynomial K :=
  (g.occurrences.map fun o => shift g.base o.shift ^ o.multiplicity).prod

def Decomposition.expand (d : Decomposition K) : Polynomial K :=
  C d.coefficient * (d.groups.map Group.expand).prod

/-- This concerns nonzero integer shifts; a nonconstant polynomial always
overlaps its own shift by zero. -/
def ShiftFree (p : Polynomial K) : Prop :=
  ∀ h : ℤ, h ≠ 0 → IsCoprime p (shift p h)

/-- Different groups are coprime at every integer shift, including zero. -/
def ShiftCoprime (p q : Polynomial K) : Prop :=
  ∀ h : ℤ, IsCoprime p (shift q h)

structure Group.Valid (g : Group K) : Prop where
  monic : g.base.Monic
  nonconstant : 0 < g.base.natDegree
  squarefree : Squarefree g.base
  shiftFree : ShiftFree g.base
  startsAtZero : (g.occurrences[0]?).map Occurrence.shift = some 0
  increasing : g.occurrences.toList.Pairwise (fun a b => a.shift < b.shift)
  positive : ∀ o ∈ g.occurrences, 0 ≤ o.shift ∧ 0 < o.multiplicity

structure Decomposition.Valid (D : Polynomial K) (d : Decomposition K) : Prop where
  coefficient_eq : d.coefficient = D.leadingCoeff
  coefficient_ne_zero : d.coefficient ≠ 0
  reconstruct : d.expand = D
  groups_valid : ∀ g ∈ d.groups, g.Valid
  separated : d.groups.toList.Pairwise (fun a b => ShiftCoprime a.base b.base)

@[simp] theorem shift_zero (p : Polynomial K) : shift p 0 = p := by
  simp [shift]

theorem shift_shift (p : Polynomial K) (a b : ℤ) : shift (shift p a) b = shift p (a + b) := by
  simp [shift, taylor_taylor, add_comm]

theorem shift_ne_zero {p : Polynomial K} (hp : p ≠ 0) (h : ℤ) : shift p h ≠ 0 :=
  (taylor_eq_zero (h : K) p).not.mpr hp

theorem Decomposition.Valid.eval {D : Polynomial K} {d : Decomposition K} (h : d.Valid D)
    (x : K) :
    D.eval x = d.coefficient * (d.groups.map fun g =>
      (g.occurrences.map fun o => g.base.eval (x + (o.shift : K)) ^ o.multiplicity).prod).prod := by
  rw [← h.reconstruct]
  simp [Decomposition.expand, Group.expand, shift, ← Array.prod_toList, Array.toList_map,
    eval_list_prod, List.map_map,
    Function.comp_def, taylor_eval]

end Gosper.ShiftlessDecomposition
