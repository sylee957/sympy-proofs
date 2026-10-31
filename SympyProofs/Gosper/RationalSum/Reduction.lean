module

public import SympyProofs.Gosper.RationalSum.Digits

/-! Reconstruction invariant of all three imperative reduction loops. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [Algebra ℚ K]

def occurrenceFraction (N : Polynomial K) (o : PreparedOccurrence) : RatFunc K :=
  (((N * o.inverse.map (algebraMap ℚ K)) %ₘ o.power.map (algebraMap ℚ K) : Polynomial K) : RatFunc K) /
    (o.power.map (algebraMap ℚ K) : RatFunc K)

def groupFraction (N : Polynomial K) (g : PreparedGroup) : RatFunc K :=
  (g.occurrences.toList.map (occurrenceFraction N)).sum

namespace Model

theorem occurrences_value (N : Polynomial K) (g : PreparedGroup) (hg : g.Valid)
    (l : List PreparedOccurrence) (hl : ∀ o ∈ l, o ∈ g.occurrences)
    (s : Array (ShiftSum K) × Array (Polynomial K)) (hs : s.2.size = g.maxMultiplicity) :
    let z := l.foldl (occurrence N g) s
    z.2.size = g.maxMultiplicity ∧
    certificateDifference z.1 + (Residual.mk g.base z.2).expand =
      certificateDifference s.1 + (Residual.mk g.base s.2).expand +
        (l.map (occurrenceFraction N)).sum := by
  induction l generalizing s with
  | nil => simpa using hs
  | cons o os ih =>
    obtain ⟨hfactor, hpower, hshift, hbound⟩ := hg.occurrences o (hl o (by simp))
    obtain ⟨hsize, hvalue⟩ := occurrence_value N g o hfactor hpower hshift hg.monic s (by omega)
    obtain ⟨hsize', hvalue'⟩ := ih (fun a ha => hl a (by simp [ha]))
      (occurrence N g s o) (hsize.trans hs)
    refine ⟨hsize', ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [hvalue', hvalue]
    simp only [occurrenceFraction, add_assoc]

theorem group_value (N : Polynomial K) (g : PreparedGroup) (hg : g.Valid)
    (s : Array (ShiftSum K) × Array (Residual K)) :
    let z := group N s g
    certificateDifference z.1 + (z.2.map Residual.expand).sum =
      certificateDifference s.1 + (s.2.map Residual.expand).sum + groupFraction N g := by
  have h := (occurrences_value N g hg g.occurrences.toList
    (fun a ha => by simpa using ha) (s.1, Array.replicate g.maxMultiplicity 0) (by simp)).2
  simp only [Residual.expand_replicate, add_zero] at h
  dsimp only [group]
  rw [Array.map_push, Array.sum_push]
  dsimp only [groupFraction] at *
  linear_combination h

theorem groups_value (N : Polynomial K) (l : List PreparedGroup)
    (hl : ∀ g ∈ l, g.Valid) (s : Array (ShiftSum K) × Array (Residual K)) :
    let z := l.foldl (group N) s
    certificateDifference z.1 + (z.2.map Residual.expand).sum =
      certificateDifference s.1 + (s.2.map Residual.expand).sum +
        (l.map (groupFraction N)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (fun a ha => hl a (by simp [ha])), group_value N g (hl g (by simp))]
    simp only [add_assoc]

end Model

theorem Result.difference_eq (r : Result K) :
    r.primitiveAt 1 - r.primitiveAt 0 =
      ((taylor 1 r.polynomialPart - r.polynomialPart : Polynomial K) : RatFunc K) +
        certificateDifference r.certificate := by
  have hs (l : List (ShiftSum K)) :
      (l.map fun s => s.expandAt 1 - s.expandAt 0).sum =
        (l.map fun s => s.expandAt 1).sum - (l.map fun s => s.expandAt 0).sum := by
    induction l with
    | nil => simp
    | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  simp only [Result.primitiveAt, certificateDifference, taylor_zero,
    ← Array.sum_toList, Array.toList_map, hs]
  simp only [RatFunc.coePolynomial, map_sub]
  ring

/-- The reduction model reconstructs the polynomial quotient and
all of its computed partial fractions. -/
theorem model_reconstruct  (p : PreparedDenominator)
    (hp : ∀ g ∈ p.groups, g.Valid) (P : Polynomial K) :
    let D := p.monicDenominator.map (algebraMap ℚ K)
    let A := C (algebraMap ℚ K p.coefficient⁻¹) * P
    let r := Model.result p P
    r.primitiveAt 1 - r.primitiveAt 0 + r.residualPart =
      ((A /ₘ D : Polynomial K) : RatFunc K) +
        (p.groups.toList.map (groupFraction (A %ₘ D))).sum := by
  dsimp only
  rw [Result.difference_eq]
  have h := Model.groups_value
    ((C (algebraMap ℚ K p.coefficient⁻¹) * P) %ₘ p.monicDenominator.map (algebraMap ℚ K))
    p.groups.toList (fun g hg => hp g (by simpa using hg)) (#[], #[])
  simp only [certificateDifference, Array.map_empty, Array.sum_empty, zero_add] at h
  have hpoly (Q : Polynomial K) :
      taylor 1 (PolynomialSum.antidifference Q) - PolynomialSum.antidifference Q = Q := by
    simpa [taylor_apply, add_comm] using PolynomialSum.antidifference_step Q
  dsimp only [Model.result, Result.residualPart]
  rw [hpoly]
  change _ + _ + _ = _
  rw [add_assoc]
  exact congrArg (_ + ·) h

end Gosper.RationalSum
