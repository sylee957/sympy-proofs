module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Basic

/-! The final product check certifies every successful exact division. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.MPoly.Raw

/-- A successful division reproduces the normalized dividend on multiplication. -/
theorem mul_of_divExact? {R : Type*} [CommRing R] [DecidableEq R] [Div R]
    {n : ℕ} {a d q : Raw R} (h : divExact? n a d = some q) :
    mul n q d = normalize n a := by
  simp only [divExact?, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, b, _, h⟩ := h
  split at h
  · cases h
    assumption
  · contradiction

end SympyProofs.Calculus.Antiderivative.MPoly.Raw

namespace SympyProofs.Calculus.Antiderivative.MPoly

/-- A checked quotient times its divisor is the dividend in the polynomial ring. -/
theorem ofRaw_mul_of_divExact? {R : Type*} [CommRing R] [DecidableEq R] [Div R]
    {n : ℕ} {a d q : Raw R} (h : Raw.divExact? n a d = some q) :
    ofRaw (n := n) q * ofRaw d = ofRaw a := by
  simpa only [ofRaw_mul, ofRaw_normalize] using congrArg (ofRaw (n := n)) (Raw.mul_of_divExact? h)

end SympyProofs.Calculus.Antiderivative.MPoly
