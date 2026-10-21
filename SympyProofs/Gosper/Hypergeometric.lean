module

public import SympyProofs.Gosper.Summability

/-!
# Hypergeometric sum ratios, equations (2) and (4)

If `σ(n) = S(n)/S(n-1)`, then the ratio of the backward differences of `S`
is `(σ(n)-1)/(1-1/σ(n-1))`. This module proves that this formulation of
hypergeometric summability is equivalent to the rational multiplier equation.
All equations here are identities of rational functions, so isolated poles
are handled separately by the finite-sum theorems' nonvanishing assumptions.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K]

/-- The sum ratio (2) and term ratio (4), excluding the zero difference. -/
def HasHypergeometricAntidifference (ρ : RatFunc K) : Prop :=
  ∃ σ : RatFunc K, σ ≠ 0 ∧ σ ≠ 1 ∧
    ρ = (σ - 1) / (1 - (rationalShift (-1) σ)⁻¹)

theorem hypergeometric_iff_rational (ρ : RatFunc K) (hρ : ρ ≠ 0) :
    HasHypergeometricAntidifference ρ ↔ HasRationalAntidifference ρ := by
  constructor
  · rintro ⟨σ, hs0, hs1, he⟩
    have hsg0 : rationalShift (-1) σ ≠ 0 :=
      fun h => hs0 ((rationalShift (-1)).injective (by simpa using h))
    have hsg1 : rationalShift (-1) σ ≠ 1 :=
      fun h => hs1 ((rationalShift (-1)).injective (by simpa using h))
    refine ⟨σ / (σ - 1), ?_⟩
    rw [he, map_div₀, map_sub, map_one]
    field_simp
  · rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := by intro h; simp [h] at hg; exact hρ hg.symm
    have hg1 : g ≠ 1 := by intro h; simp [h] at hg
    have hsg0 : rationalShift (-1) g ≠ 0 :=
      fun h => hg0 ((rationalShift (-1)).injective (by simpa using h))
    have hsg1 : rationalShift (-1) g ≠ 1 :=
      fun h => hg1 ((rationalShift (-1)).injective (by simpa using h))
    let σ := g / (g - 1)
    have hs0 : σ ≠ 0 := div_ne_zero hg0 (sub_ne_zero.mpr hg1)
    have hs1 : σ ≠ 1 := by
      intro h
      have he := (div_eq_one_iff_eq (sub_ne_zero.mpr hg1)).mp h
      have : (1 : RatFunc K) = 0 := by linear_combination he
      exact one_ne_zero this
    refine ⟨σ, hs0, hs1, ?_⟩
    dsimp [σ]
    rw [map_div₀, map_sub, map_one]
    field_simp
    linear_combination hg

variable [DecidableEq K]

/-- The paper's decision criterion in terms of the hypergeometric sum ratio. -/
theorem hypergeometric_gosper_criterion [CharZero K] (p q r : K[X])
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
theorem no_hypergeometric_antidifference_of_degreeBound_neg [CharZero K] (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r)
    (hk : paperDegreeBound p (taylor 1 q) r < 0) :
    ¬HasHypergeometricAntidifference (normalRatio p q r) := by
  intro h
  exact (not_le_of_gt hk) ((hypergeometric_gosper_criterion p q r hp hq hr hqr).mp h).1

end Gosper
