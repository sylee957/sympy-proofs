module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Cover
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Infinity
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Reconstruction

/-! Characterization of saturated logarithmic derivatives with a squarefree denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial Differential
open scoped Polynomial

variable {E F : Type*} [Field E] [Field F] [CharZero F]
variable [Differential F] [Differential (RatFunc F)] [DifferentialAlgebra F (RatFunc F)]
local notation "ι" => algebraMap F[X] (RatFunc F)

omit [CharZero F] in
private theorem saturated_C {c : F} (hc : Saturated deriv c) :
    Saturated deriv (RatFunc.C c) := by
  obtain ⟨m, y, hm, hy, h⟩ := hc
  refine ⟨m, RatFunc.C y, hm, (map_ne_zero_iff _ RatFunc.C_injective).mpr hy, ?_⟩
  change deriv (algebraMap F (RatFunc F) y) / _ = _
  rw [deriv_algebraMap]
  change RatFunc.C (deriv y) / RatFunc.C y = _
  rw [← map_div₀, h, map_mul, map_natCast]

/-- The polynomial part descends to a lower logarithmic relation up to the linear
velocity. The simple proper part is characterized by rational residues at the ground
irreducibles, even when the coefficient extension splits those irreducibles. -/
theorem saturated_iff (j : E →+* F) {a b : F}
    (dx : deriv (RatFunc.X : RatFunc F) = RatFunc.C a * RatFunc.X + RatFunc.C b)
    (tw : Saturated deriv (RatFunc.C a))
    (lead : ∀ p : F[X], p.Monic →
      (Extension.affine a b p - C ((p.natDegree : F) * a) * p).degree < p.degree)
    (N S DS : E[X]) (ps : List E[X]) (hS : S ≠ 0) (sf : Squarefree (S.map j))
    (normal : ∀ p : F[X], Prime p → p ∣ S.map j → ¬ p ∣ Extension.affine a b p)
    (der : DS.map j = Extension.affine a b (S.map j))
    (prod : C S.leadingCoeff * ps.prod = S) (irr : ∀ p ∈ ps, Irreducible p)
    (c : E) (hc : (N / S).coeff 0 = c) :
    Saturated deriv (ι (N.map j) / ι (S.map j)) ↔
      N / S = C c ∧ (∀ p ∈ ps, ∃ r : ℚ, p ∣ N - C (r : E) * DS) ∧
        ∃ e : ℚ, Saturated deriv (j c + (e : F) * a) := by
  classical
  have hs := (Polynomial.map_ne_zero_iff j.injective).mpr hS
  constructor
  · intro h
    obtain ⟨c₀, r, h₀, hp⟩ := infinity_of_saturated dx h
    have eq := polynomial_part hs _ hp
    rw [← Polynomial.map_div] at eq
    have jc : j c = c₀ + (r : F) * a := by
      simpa only [Polynomial.coeff_map, hc, Polynomial.coeff_C_zero] using congrArg (·.coeff 0) eq
    refine ⟨Polynomial.map_injective j j.injective (by rwa [Polynomial.map_C, jc]), ?_, -r, ?_⟩
    · intro p hpm
      have deg := (irr p hpm).natDegree_pos
      have nu := (p.map j).not_isUnit_of_natDegree_pos (by simpa using deg)
      obtain ⟨s, _, si, hsp⟩ := Polynomial.exists_monic_irreducible_factor _ nu
      have hps : p ∣ S := prod ▸ (List.dvd_prod hpm).trans (dvd_mul_left _ _)
      obtain ⟨q, hq⟩ := residue_of_saturated dx _ _ hs h si.prime
        (hsp.trans (Polynomial.map_dvd j hps))
      refine ⟨q, descend_dvd j (irr p hpm) si.prime hsp ?_⟩
      simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, map_ratCast, der]
        using hq
    · simpa only [jc, Rat.cast_neg, neg_mul, add_neg_cancel_right] using h₀
  · rintro ⟨eq, ground, e, he⟩
    obtain ⟨rs, hr⟩ := (residue_cover_iff j N DS S ps hS prod irr).mp ground
    have hproper := saturated_of_residues (Extension.affine a b) deriv
      (Extension.LiouvilleForm.affineDeriv_map dx) a tw lead ((N.map j) % (S.map j)) (S.map j) sf
      (Polynomial.degree_mod_lt _ hs) normal rs (by
        intro p hp hd
        obtain ⟨r, hmem, h⟩ := hr p hp hd
        rw [der] at h
        exact ⟨r, hmem, residue_mod _ _ _ _ hd h⟩)
    have const := (saturated_C he).add ((tw.rat_mul e).neg)
    have hc' : Saturated deriv (RatFunc.C (j c)) := by
      simpa only [map_add, map_mul, map_ratCast, add_neg_cancel_right] using const
    convert hproper.add hc' using 1
    have eq' := congrArg (Polynomial.map j) eq
    rw [Polynomial.map_div, Polynomial.map_C] at eq'
    have h := congrArg ι (EuclideanDomain.mod_add_div (N.map j) (S.map j))
    rw [eq', map_add, map_mul, RatFunc.algebraMap_C] at h
    field_simp [RatFunc.algebraMap_ne_zero hs]
    linear_combination -h

end SympyProofs.Calculus.Antiderivative.Logarithmic
