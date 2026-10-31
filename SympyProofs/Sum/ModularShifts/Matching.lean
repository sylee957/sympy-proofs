module

public import SympyProofs.Sum.ModularShifts.Centering
public import Std.Tactic.Do
public import Std.WP

/-! Loop invariants for centered-factor matching and duplicate elimination. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial
open scoped Std.WP

/-- The final loop of `shifts`, isolated here for its invariant proof. -/
def matchFactors {m : ℕ} (p q : Polynomial ℤ)
    (fs gs : Array (Polynomial (ZMod m))) : Array ℤ := Id.run do
  let mut found := #[]
  for f in fs do
    let cf := center f
    for g in gs do
      if f.natDegree = g.natDegree ∧ cf = center g then
        let h := ((f.nextCoeff - g.nextCoeff) * (f.natDegree : ZMod m)⁻¹).valMinAbs
        if 0 < (GCDMonoid.gcd p (taylor h q)).natDegree ∧ h ∉ found then
          found := found.push h
  return found

/-- A matching pair that survives the exact integer gcd test. -/
def PairProduces {m : ℕ} (p q : Polynomial ℤ)
    (f g : Polynomial (ZMod m)) (h : ℤ) : Prop :=
  f.natDegree = g.natDegree ∧ center f = center g ∧
    ((f.nextCoeff - g.nextCoeff) * (f.natDegree : ZMod m)⁻¹).valMinAbs = h ∧
    0 < (GCDMonoid.gcd p (taylor h q)).natDegree

theorem matchFactors_spec {m : ℕ} (p q : Polynomial ℤ)
    (fs gs : Array (Polynomial (ZMod m))) :
    (matchFactors p q fs gs).toList.Nodup ∧
      ∀ h, h ∈ matchFactors p q fs gs ↔
        ∃ f ∈ fs, ∃ g ∈ gs, PairProduces p q f g h := by
  generalize he : matchFactors p q fs gs = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ found => found.toList.Nodup ∧
      ∀ h, h ∈ found ↔ ∃ f ∈ pref, ∃ g ∈ gs, PairProduces p q f g h
  · by
      rename_i pref f suff hs old hi
      exact fun pref _ found => found.toList.Nodup ∧
        ∀ h, h ∈ found ↔ h ∈ old ∨ ∃ g ∈ pref, PairProduces p q f g h
  all_goals simp_all [PairProduces]
  all_goals grind

end Gosper.ModularShifts
