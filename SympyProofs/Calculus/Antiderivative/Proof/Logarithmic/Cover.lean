module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Local

/-! A finite rational residue cover is unchanged by extending the coefficient field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial
open scoped Polynomial

private theorem finite_choices {α β : Type*} (ps : List α) (P : α → β → Prop)
    (h : ∀ p ∈ ps, ∃ q, P p q) : ∃ s : Finset β, ∀ p ∈ ps, ∃ q ∈ s, P p q := by
  classical
  induction ps with
  | nil => exact ⟨∅, by simp⟩
  | cons a as ih =>
    obtain ⟨r, hr⟩ := h a List.mem_cons_self
    obtain ⟨s, hs⟩ := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
    refine ⟨insert r s, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨r, Finset.mem_insert_self .., hr⟩
    · obtain ⟨r, hr, he⟩ := hs _ hp
      exact ⟨r, Finset.mem_insert_of_mem hr, he⟩

private theorem dvd_factor {E F : Type*} [Field E] [Field F] (j : E →+* F) {u : F[X]}
    (hu : Prime u) (ps : List E[X]) (h : u ∣ ps.prod.map j) :
    ∃ p ∈ ps, u ∣ p.map j := by
  induction ps with
  | nil => simp [hu.not_dvd_one] at h
  | cons p ps ih =>
    rw [List.prod_cons, Polynomial.map_mul] at h
    rcases hu.dvd_or_dvd h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, h⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

/-- Rational residues at the ground irreducibles yield a finite rational cover at every
prime above them, and conversely a residue found above descends by Bézout. -/
theorem residue_cover_iff {E F : Type*} [Field E] [Field F] (j : E →+* F)
    (N D S : E[X]) (ps : List E[X]) (hs : S ≠ 0) (prod : C S.leadingCoeff * ps.prod = S)
    (irr : ∀ p ∈ ps, Irreducible p) :
    (∀ p ∈ ps, ∃ r : ℚ, p ∣ N - C (r : E) * D) ↔
      ∃ rs : Finset ℚ, ∀ s : F[X], Prime s → s ∣ S.map j →
        ∃ r ∈ rs, s ∣ N.map j - C (r : F) * D.map j := by
  constructor
  · intro ground
    obtain ⟨rs, hr⟩ := finite_choices ps _ ground
    refine ⟨rs, fun s hp hd => ?_⟩
    have eq := congrArg (Polynomial.map j) prod
    rw [Polynomial.map_mul, Polynomial.map_C] at eq
    have hl := (map_ne_zero_iff j j.injective).mpr (leadingCoeff_ne_zero.mpr hs)
    have unit := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hl)
    rw [← eq, unit.dvd_mul_left] at hd
    obtain ⟨p, hpm, hp'⟩ := dvd_factor j hp ps hd
    obtain ⟨r, hmem, hdiv⟩ := hr p hpm
    exact ⟨r, hmem, hp'.trans (by simpa using Polynomial.map_dvd j hdiv)⟩
  · rintro ⟨rs, hr⟩ p hp
    have pos := (irr p hp).natDegree_pos
    have unit : ¬ IsUnit (p.map j) := (p.map j).not_isUnit_of_natDegree_pos (by simpa using pos)
    obtain ⟨s, _, hi, hsp⟩ := Polynomial.exists_monic_irreducible_factor _ unit
    have hps : p ∣ S := prod ▸ (List.dvd_prod hp).trans (dvd_mul_left _ _)
    obtain ⟨r, _, he⟩ := hr s hi.prime (hsp.trans (Polynomial.map_dvd j hps))
    exact ⟨r, descend_dvd j (irr p hp) hi.prime hsp (by simpa using he)⟩

/-- Subtracting a polynomial part changes the numerator by a multiple of every factor of
the denominator, leaving the local residue congruence invariant. -/
theorem residue_mod {F : Type*} [Field F] (N S D q : F[X]) {p : F[X]} (hp : p ∣ S)
    (hd : p ∣ N - q * D) : p ∣ N % S - q * D := by
  have h := EuclideanDomain.mod_add_div N S
  have he : N % S - q * D = (N - q * D) - S * (N / S) := by linear_combination h
  rw [he]
  exact dvd_sub hd (hp.mul_right (N / S))

end SympyProofs.Calculus.Antiderivative.Logarithmic
