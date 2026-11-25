module

public import SympyProofs.Calculus.Risch.Program.Poly
public import SympyProofs.Calculus.Risch.Spec.Field

/-! The polynomial that a coefficient list denotes. A list of terms of depth `n`, lowest
degree first, is a polynomial in the newest generator over the field `K k n`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Poly

open Polynomial

variable {n : ℕ}

/-- The polynomial over the field of depth `n` that a coefficient list denotes. -/
noncomputable def model (k : Type) [Field k] [CharZero k] : Poly n → (K k n)[X]
  | [] => 0
  | c :: cs => C (Term.value k c) + X * model k cs

end SympyProofs.Calculus.Risch.Poly
