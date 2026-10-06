import Mathlib.Tactic

/-! Ring identities for the descending-coefficient pseudo-remainder. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
/-- Numerator of the next row, after cancellation of the two leading terms. -/
def numerator {R : Type*} [CommRing R] (u v : ℕ → R) (j : ℕ) : R :=
  v 0 ^ 2 * u (j+2) - (v 0*u 1-u 0*v 1)*v (j+1) - u 0*v 0*v (j+2)

/-- Clearing the ordinary complex elimination denominators gives `numerator`.
No order, conjugation, or positivity assumption is needed for this identity. -/
theorem numerator_eq {K : Type*} [Field K] (u v : ℕ → K) (hv : v 0 ≠ 0) (j : ℕ) :
    numerator u v j = v 0^2 *
      (u (j+2) - ((u 1-u 0/v 0*v 1)/v 0)*v (j+1) - (u 0/v 0)*v (j+2)) := by
  unfold numerator
  field_simp

/-- Two consecutive unnormalized pseudo-remainders contain the square of the
intermediate pivot as an exact factor (the local cancellation behind the
G-sequence). This does not assume a field, nonzero pivots, or integral-domain
cancellation. -/
theorem previousPivot_sq_dvd {R : Type*} [CommRing R] (u v : ℕ → R) (j : ℕ) :
    v 0^2 ∣ numerator v (numerator u v) j := by
  let a := u 0
  let a1 := u 1
  let a2 := u 2
  let a3 := u 3
  let b := v 0
  let b1 := v 1
  let b2 := v 2
  let b3 := v 3
  let A3 := u (j+3)
  let A4 := u (j+4)
  let B2 := v (j+2)
  let B3 := v (j+3)
  let B4 := v (j+4)
  refine ⟨
    -A3*a*b1^3 - B2*a^2*b1*b3 + B2*a^2*b2^2 - B2*a*a1*b1*b2
      + B2*a*a2*b1^2 - B3*a^2*b1*b2 + B3*a*a1*b1^2 + B4*a^2*b1^2
      + b^3*(A3*a3 - A4*a2)
      + b^2*(-A3*a*b3 - A3*a1*b2 - A3*a2*b1 + A4*a*b2 + A4*a1*b1
        - B2*a1*a3 + B2*a2^2 - B3*a*a3 + B3*a1*a2 + B4*a*a2)
      + b*(2*A3*a*b1*b2 + A3*a1*b1^2 - A4*a*b1^2 + B2*a*a1*b3
        - 2*B2*a*a2*b2 + B2*a*a3*b1 + B2*a1^2*b2 - B2*a1*a2*b1
        + B3*a^2*b3 - B3*a1^2*b1 - B4*a^2*b2 - B4*a*a1*b1), ?_⟩
  dsimp [numerator, a, a1, a2, a3, b, b1, b2, b3, A3, A4, B2, B3, B4]
  simp only [Nat.add_assoc]
  ring

end RouthHurwitz.ComplexRouth.FractionFree
