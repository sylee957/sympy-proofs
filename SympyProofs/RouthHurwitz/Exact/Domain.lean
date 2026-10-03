import Mathlib

/-! Exact coefficient arithmetic is separate from its real interpretation. -/
namespace RouthHurwitz.Exact

/-- A real interpretation compatible with the coefficient domain's order.
Used only by correctness proofs; the runner uses the domain's own comparisons. -/
structure RealDomain (A : Type*) [CommRing A] [LinearOrder A] where
  embed : A →+* ℝ
  strictMono : StrictMono embed

theorem RealDomain.injective [CommRing A] [LinearOrder A] (D : RealDomain A) :
    Function.Injective D.embed := D.strictMono.injective

def integers : RealDomain ℤ where
  embed := Int.castRingHom ℝ
  strictMono := by
    intro a b h
    change (a : ℝ) < (b : ℝ)
    exact_mod_cast h

noncomputable def rationals : RealDomain ℚ where
  embed := Rat.castHom ℝ
  strictMono := by
    intro a b h
    change (a : ℝ) < (b : ℝ)
    exact_mod_cast h

/-- Transport an exact quotient through an injective field interpretation. -/
theorem map_quotient {A K : Type*} [CommRing A] [Div A] [MulDivCancelClass A] [Field K]
    (f : A →+* K) (hf : Function.Injective f) (a d : A)
    (hd : d ≠ 0) (ha : d ∣ a) : f (a / d) = f a / f d := by
  obtain ⟨q, rfl⟩ := ha
  rw [mul_div_cancel_left₀ _ hd, map_mul, mul_div_cancel_left₀ _]
  exact fun h => hd (hf (h.trans (map_zero f).symm))

end RouthHurwitz.Exact
