module

public import SympyProofs.Gosper.RationalSum.Basic
public import SympyProofs.Gosper.PolynomialSum.Correctness
public import SympyProofs.Gosper.ShiftlessDecomposition.Basic
public import Std.Tactic.Do
public import Std.WP

/-! Fold descriptions used only in proofs of the imperative reducer. -/

@[expose] public section
noncomputable section

namespace Gosper.RationalSum
open Polynomial
open scoped Classical

/-- Denominator-only data for one occurrence `base(X+shift)^multiplicity`. -/
structure PreparedOccurrence where
  shift : ℤ
  multiplicity : ℕ
  factor : Polynomial ℚ
  power : Polynomial ℚ
  inverse : Polynomial ℚ

structure PreparedGroup where
  base : Polynomial ℚ
  maxMultiplicity : ℕ
  occurrences : Array PreparedOccurrence

structure PreparedDenominator where
  coefficient : ℚ
  monicDenominator : Polynomial ℚ
  groups : Array PreparedGroup

namespace Model

def prepareOccurrence (D : Polynomial ℚ) (g : ShiftlessDecomposition.Group ℚ)
    (o : ShiftlessDecomposition.Occurrence) : PreparedOccurrence :=
  let f := taylor (o.shift : ℚ) g.base
  let F := f ^ o.multiplicity
  let (d, u, _) := EuclideanDomain.xgcdAux (D / F) 1 0 F 0 1
  ⟨o.shift, o.multiplicity, f, F, (C d.leadingCoeff⁻¹ * u) % F⟩

def prepareGroup (D : Polynomial ℚ) (g : ShiftlessDecomposition.Group ℚ) : PreparedGroup :=
  ⟨g.base, (g.occurrences.toList.map (·.multiplicity)).foldl max 0,
    g.occurrences.map (prepareOccurrence D g)⟩

end Model

/-- Proof-only description of the denominator data used inside `reduce`. -/
def prepare (D : Polynomial ℚ) (d : Array (ShiftlessDecomposition.Group ℚ)) :
    PreparedDenominator :=
  { coefficient := D.leadingCoeff
    monicDenominator := C D.leadingCoeff⁻¹ * D
    groups := d.map (Model.prepareGroup (C D.leadingCoeff⁻¹ * D)) }

variable {R : Type*} [CommRing R] [Algebra ℚ R]

namespace Model

def digit (g : PreparedGroup) (o : PreparedOccurrence)
    (s : Array (ShiftSum R) × Array (Polynomial R) × Polynomial R) (j : ℕ) :=
  let k := o.multiplicity - j
  let a := taylor ((-o.shift : ℤ) : R) (s.2.2 %ₘ o.factor.map (algebraMap ℚ R))
  let n := s.2.1.modify (k - 1) (· + a)
  let A := s.2.2 /ₘ o.factor.map (algebraMap ℚ R)
  if 0 < o.shift then (s.1.push ⟨a, g.base ^ k, o.shift.toNat⟩, n, A)
  else (s.1, n, A)

def occurrence (N : Polynomial R) (g : PreparedGroup)
    (s : Array (ShiftSum R) × Array (Polynomial R)) (o : PreparedOccurrence) :=
  let z := (List.range o.multiplicity).foldl (digit g o)
    (s.1, s.2, (N * o.inverse.map (algebraMap ℚ R)) %ₘ o.power.map (algebraMap ℚ R))
  (z.1, z.2.1)

def group (N : Polynomial R) (s : Array (ShiftSum R) × Array (Residual R))
    (g : PreparedGroup) :=
  let z := g.occurrences.toList.foldl (occurrence N g)
    (s.1, Array.replicate g.maxMultiplicity 0)
  (z.1, s.2.push ⟨g.base, z.2⟩)

def result (p : PreparedDenominator) (P : Polynomial R) : Result R :=
  let D := p.monicDenominator.map (algebraMap ℚ R)
  let A := C (algebraMap ℚ R p.coefficient⁻¹) * P
  let s := p.groups.toList.foldl (group (A %ₘ D)) (#[], #[])
  ⟨PolynomialSum.antidifference (A /ₘ D), s.1, s.2⟩

end Model


end Gosper.RationalSum
