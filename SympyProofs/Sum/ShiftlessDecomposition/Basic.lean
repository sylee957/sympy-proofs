module

public import SympyProofs.Sum.ShiftlessDecomposition.Algorithm

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

def Group.expand (g : Group K) : Polynomial K :=
  (g.occurrences.map fun o => taylor (o.shift : K) g.base ^ o.multiplicity).prod

/-- This concerns nonzero integer shifts; a nonconstant polynomial always
overlaps its own shift by zero. -/
def ShiftFree (p : Polynomial K) : Prop :=
  ∀ h : ℤ, h ≠ 0 → IsCoprime p (taylor (h : K) p)

/-- Different groups are coprime at every integer shift, including zero. -/
def ShiftCoprime (p q : Polynomial K) : Prop :=
  ∀ h : ℤ, IsCoprime p (taylor (h : K) q)

structure Group.Valid (g : Group K) : Prop where
  monic : g.base.Monic
  nonconstant : 0 < g.base.natDegree
  squarefree : Squarefree g.base
  shiftFree : ShiftFree g.base
  startsAtZero : (g.occurrences[0]?).map Occurrence.shift = some 0
  increasing : g.occurrences.toList.Pairwise (fun a b => a.shift < b.shift)
  positive : ∀ o ∈ g.occurrences, 0 ≤ o.shift ∧ 0 < o.multiplicity

/-- Correctness of an array of shiftless groups for the original input. -/
structure Valid (D : Polynomial K) (groups : Array (Group K)) : Prop where
  nonzero : D ≠ 0
  reconstruct : C D.leadingCoeff * (groups.map Group.expand).prod = D
  groups_valid : ∀ g ∈ groups, g.Valid
  separated : groups.toList.Pairwise (fun a b => ShiftCoprime a.base b.base)

theorem Valid.eval {D : Polynomial K} {groups : Array (Group K)} (h : Valid D groups)
    (x : K) :
    D.eval x = D.leadingCoeff * (groups.map fun g =>
      (g.occurrences.map fun o => g.base.eval (x + (o.shift : K)) ^ o.multiplicity).prod).prod := by
  conv_lhs => rw [← h.reconstruct]
  simp [Group.expand, ← Array.prod_toList, Array.toList_map,
    eval_list_prod, List.map_map,
    Function.comp_def, taylor_eval]

end Gosper.ShiftlessDecomposition
