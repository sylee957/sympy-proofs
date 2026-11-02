module

public import SympyProofs.Sum.Gosper.Summability

/-!
# Hypergeometric antidifferences in the forward convention

If `σ(n) = S(n+1)/S(n)` and `a(n) = S(n+1)-S(n)`, then the forward term ratio
`ρ(n) = a(n+1)/a(n)` satisfies `ρ(n)(σ(n)-1) = σ(n)(σ(n+1)-1)`.
This module connects that formula to both rational multiplier conventions.
All equations here are identities of rational functions, so isolated poles
are handled separately by the finite-sum theorems' nonvanishing assumptions.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [CommRing K] [IsDomain K]

/-- A nonzero forward difference of a hypergeometric sum, expressed without division. -/
def HasHypergeometricAntidifference (ρ : RatFunc K) : Prop :=
  ∃ σ : RatFunc K, σ ≠ 0 ∧ σ ≠ 1 ∧
    ρ * (σ - 1) = σ * (rationalShift 1 σ - 1)

/-- Summability is unchanged by an equivalence that preserves translation. -/
theorem hasHypergeometricAntidifference_equiv
    {R : Type*} [CommRing R] [IsDomain R] (e : RatFunc K ≃+* RatFunc R)
    (hshift : ∀ f, e (rationalShift 1 f) = rationalShift 1 (e f)) (ρ : RatFunc K) :
    HasHypergeometricAntidifference ρ ↔ HasHypergeometricAntidifference (e ρ) := by
  constructor
  · rintro ⟨σ, hσ0, hσ1, he⟩
    refine ⟨e σ, by simpa using hσ0, by simpa using hσ1, ?_⟩
    simpa only [map_mul, map_sub, map_one, hshift] using congrArg e he
  · rintro ⟨σ, hσ0, hσ1, he⟩
    obtain ⟨σ, rfl⟩ := e.surjective σ
    refine ⟨σ, by simpa using hσ0, by simpa using hσ1, e.injective ?_⟩
    simpa only [map_mul, map_sub, map_one, hshift] using he

/-- The forward sum-ratio formula is equivalent to the forward multiplier equation. -/
theorem hypergeometric_iff_forward (ρ : RatFunc K) (hρ : ρ ≠ 0) :
    HasHypergeometricAntidifference ρ ↔
      ∃ g : RatFunc K, ρ * rationalShift 1 g - g = 1 := by
  constructor
  · rintro ⟨σ, hs0, hs1, he⟩
    have hsg1 : rationalShift 1 σ ≠ 1 :=
      fun h => hs1 ((rationalShift 1).injective (by simpa using h))
    have hratio := (eq_div_iff (sub_ne_zero.mpr hs1)).mpr he
    refine ⟨(σ - 1)⁻¹, ?_⟩
    rw [hratio, map_inv₀, map_sub, map_one]
    field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr hsg1]
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := by
      intro h
      simp [h] at hg
    have hgadd : g + 1 ≠ 0 := by
      intro h
      have he : g = -1 := by linear_combination h
      rw [he] at hg
      simp only [map_neg, map_one, mul_neg_one, sub_neg_eq_add] at hg
      apply hρ
      linear_combination -hg
    let σ := (g + 1) / g
    have hs0 : σ ≠ 0 := div_ne_zero hgadd hg0
    have hs1 : σ ≠ 1 := by
      intro h
      have he := (div_eq_one_iff_eq hg0).mp h
      have : (1 : RatFunc K) = 0 := by linear_combination he
      exact one_ne_zero this
    refine ⟨σ, hs0, hs1, ?_⟩
    dsimp [σ]
    rw [map_div₀, map_add, map_one]
    have hsg0 : rationalShift 1 g ≠ 0 :=
      fun h => hg0 ((rationalShift 1).injective (by simpa using h))
    field_simp [hg0, hsg0]
    linear_combination hg

/-- The forward formulation also characterizes the paper's rational multiplier equation. -/
theorem hypergeometric_iff_rational (ρ : RatFunc K) (hρ : ρ ≠ 0) :
    HasHypergeometricAntidifference ρ ↔ HasRationalAntidifference ρ := by
  rw [hypergeometric_iff_forward ρ hρ]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨rationalShift 1 g + 1, ?_⟩
    simp only [map_add, map_one, rationalShift_add, neg_add_cancel, rationalShift_zero]
    linear_combination hg
  · rintro ⟨h, hh⟩
    refine ⟨rationalShift (-1) h - 1, ?_⟩
    simp only [map_sub, map_one, rationalShift_add, add_neg_cancel, rationalShift_zero]
    linear_combination hh

variable {F : Type*} [Field F] [DecidableEq F]

/-- The paper's decision criterion in terms of the hypergeometric sum ratio. -/
theorem hypergeometric_gosper_criterion [CharZero F] (p q r : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r) :
    HasHypergeometricAntidifference (normalRatio p q r) ↔
      let k := paperDegreeBound p (taylor 1 q) r
      0 ≤ k ∧ ∃ c, (coefficientMatrix p q r k.toNat).mulVec c =
        toFn (equationDegree p q r k.toNat + 1) p := by
  have hρ : normalRatio p q r ≠ 0 := by
    unfold normalRatio
    apply div_ne_zero
    · simpa using mul_ne_zero hp hq
    · simpa using mul_ne_zero ((taylor_eq_zero (-1) p).not.mpr hp) hr
  rw [hypergeometric_iff_rational _ hρ, gosper_criterion p q r hp hq hr hqr]

/-- A negative degree bound excludes a hypergeometric antidifference. -/
theorem no_hypergeometric_antidifference_of_degreeBound_neg [CharZero F] (p q r : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r)
    (hk : paperDegreeBound p (taylor 1 q) r < 0) :
    ¬HasHypergeometricAntidifference (normalRatio p q r) := by
  intro h
  exact (not_le_of_gt hk) ((hypergeometric_gosper_criterion p q r hp hq hr hqr).mp h).1

end Gosper
