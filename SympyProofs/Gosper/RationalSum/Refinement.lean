module

public import SympyProofs.Gosper.RationalSum.Model

/-! The imperative polynomial reducer equals its fold model. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Std.WP
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem reduce_eq_model (ops : ShiftlessDecomposition.Primitives ℚ)
    (P : Polynomial R) (D : Polynomial ℚ) :
    reduce ops P D = Model.result (prepare D (ShiftlessDecomposition.decompose ops D)) P := by
  generalize he : reduce ops P D = out
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ s => s = (pref.map (Model.prepareGroup monicDenominator)).foldl
      (Model.group N) (#[], #[])
  · by
      rename_i gp g gs hg cs rs hi
      exact fun pref _ m => m.down = (pref.map (·.multiplicity)).foldl max 0
  · by
      rename_i gp g gs hg cs rs hi m hm
      exact fun pref _ s => s = (pref.map (Model.prepareOccurrence monicDenominator g)).foldl
        (Model.occurrence N (Model.prepareGroup monicDenominator g)) (cs, numerators)
  · by
      rename_i gp g gs hg cs rs hi m hm op o os ho cs ns hi
      exact fun pref _ s => s = pref.foldl
        (Model.digit (Model.prepareGroup monicDenominator g)
          (Model.prepareOccurrence monicDenominator g o)) (cs, ns, A)
  case vc1 | vc3 | vc4 | vc6 => rfl
  case vc2 =>
    rename_i cs rs hi
    simp only [Std.Internal.ForIn.toList_array] at hi
    simp only [Model.result, prepare, Array.toList_map]
    change Result.mk polynomialPart cs rs = Result.mk polynomialPart
      ((groups.toList.map (Model.prepareGroup monicDenominator)).foldl
        (Model.group N) (#[], #[])).1
      ((groups.toList.map (Model.prepareGroup monicDenominator)).foldl
        (Model.group N) (#[], #[])).2
    rw [← hi]
  case vc5 =>
    rename_i gp g gs hg cs rs hi m hm cs' ns ho
    simp only [Std.Internal.ForIn.toList_array] at ho hm
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← hi, Model.group, Model.prepareGroup,
      Array.toList_map, ← hm]
    simp only [Model.prepareGroup, ← hm] at ho
    rw [← ho]
  case vc7 =>
    rename_i gp g gs hg cs rs hi m hm op o os ho cs ns hi cs' ns' A' hd state
    simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range'] at hd
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← hi, Model.occurrence]
    change (cs', ns') = ((List.foldl _ (cs, ns, A) (List.range o.multiplicity)).1,
      (List.foldl _ (cs, ns, A) (List.range o.multiplicity)).2.1)
    rw [← hd]
  case vc8 | vc9 =>
    rename_i gp g gs hg cs rs hi m hm op o os ho cs ns hi jp j js hj cs' ns' a ha state oldDigit hpos
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← ha]
    simp only [Model.digit, Model.prepareOccurrence, Model.prepareGroup, hpos, ite_true, ite_false]
    rfl
  case vc10 =>
    simp_all only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

end Gosper.RationalSum
