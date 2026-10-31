module

public import SympyProofs.Gosper.RationalSum.Specialization
public import SympyProofs.Gosper.ShiftlessDecomposition.Shifts

/-! Invariants of the proof-only denominator model. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical
open scoped Std.WP

theorem prepare_eq_model (D : Polynomial ℚ) (d : Array (ShiftlessDecomposition.Group ℚ)) :
    prepare D d = {
      coefficient := D.leadingCoeff
      monicDenominator := C D.leadingCoeff⁻¹ * D
      groups := d.map (Model.prepareGroup (C D.leadingCoeff⁻¹ * D)) } := rfl

/-- Preparation produces monic divisors even when later numerator specializations
drop degree or introduce zero divisors in the coefficient algebra. -/
theorem prepare_monic {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) : (prepare D d).Monic := by
  have hD : D ≠ 0 := hd.nonzero
  rw [prepare_eq_model]
  refine ⟨?_, ?_⟩
  · simpa [mul_comm] using monic_mul_leadingCoeff_inv hD
  · intro g hg o ho
    obtain ⟨g, hgm, rfl⟩ := Array.mem_map.mp hg
    obtain ⟨o, hom, rfl⟩ := Array.mem_map.mp ho
    have hm := (hd.groups_valid g hgm).monic
    have ht : (taylor (o.shift : ℚ) g.base).Monic := by simpa [Monic] using hm
    exact ⟨ht, ht.pow _⟩

/-- Structural facts used by the nested numerator-extraction loops. -/
structure PreparedGroup.Valid (g : PreparedGroup) : Prop where
  monic : g.base.Monic
  occurrences : ∀ o ∈ g.occurrences,
    o.factor = taylor (o.shift : ℚ) g.base ∧
    o.power = o.factor ^ o.multiplicity ∧
    0 ≤ o.shift ∧ o.multiplicity ≤ g.maxMultiplicity

private theorem le_foldl_max (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl max a ∧ ∀ n ∈ l, n ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons n ns ih =>
    obtain ⟨ha, hn⟩ := ih (max a n)
    refine ⟨(le_max_left a n).trans ha, ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (le_max_right a m).trans ha
    · exact hn m hm

theorem prepare_groups_valid {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (g : PreparedGroup) (hg : g ∈ (prepare D d).groups) : g.Valid := by
  rw [prepare_eq_model] at hg
  obtain ⟨g, hgm, rfl⟩ := Array.mem_map.mp hg
  refine ⟨(hd.groups_valid g hgm).monic, ?_⟩
  intro o ho
  obtain ⟨o, hom, rfl⟩ := Array.mem_map.mp ho
  refine ⟨rfl, rfl, (hd.groups_valid g hgm).positive o hom |>.1, ?_⟩
  apply (le_foldl_max (g.occurrences.toList.map (·.multiplicity)) 0).2
  exact List.mem_map.mpr ⟨o, by simpa using hom, rfl⟩

/-- The reduction model commutes with arbitrary parameter specialization. -/
theorem model_prepare_map {R S : Type*} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial R) :
    Model.result (prepare D d) (P.map f.toRingHom) = (Model.result (prepare D d) P).map f :=
  model_map f _ (prepare_monic hd) P

/-- Parameters may be arbitrary functions on any parameter space. -/
theorem model_prepare_apply {Θ R : Type*} [CommRing R] [Algebra ℚ R]

    {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial (Θ → R)) (θ : Θ) :
    Model.result (prepare D d) (P.map (Pi.evalRingHom (fun _ : Θ => R) θ)) =
      (Model.result (prepare D d) P).map (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) :=
  model_prepare_map (Pi.evalAlgHom ℚ (fun _ : Θ => R) θ) hd P


end Gosper.RationalSum
