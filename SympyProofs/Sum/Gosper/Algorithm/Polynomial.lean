module

public import Mathlib

/-!
# Polynomial operations over the coefficient field

The algorithm uses `Polynomial K` directly. Addition, multiplication, quotient,
remainder, gcd, translation, and resultant correspond to the operations exposed
by SymPy's polynomial layer (`dup_*` / `dmp_*` below its public API). Their dense
or sparse representation is not part of the Gosper model.

The coefficient field has characteristic zero, so the integer and natural casts
are injective. Decidable `IsLocalization.IsInteger ℤ` membership and
`Encodable.choose` recognize and recover integer coefficients constructively.
Mathlib's polynomial division and factorization remain
noncomputable; `Backend.Basic` specifies the replaceable CAS operations.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- A reduced rational belongs to the integer image exactly when its denominator is one. -/
theorem rat_isInteger_iff_den_eq_one (q : ℚ) : IsInteger ℤ q ↔ q.den = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact Rat.den_intCast z
  · intro h
    exact ⟨q.num, Rat.coe_int_num_of_den_eq_one h⟩

/-- Decide integer membership over the rational coefficient field without classical choice. -/
instance ratDecidableIsInteger : DecidablePred (IsInteger ℤ : ℚ → Prop) := fun q =>
  decidable_of_iff (q.den = 1) (rat_isInteger_iff_den_eq_one q).symm

variable {K : Type*} [Field K]

def monic (p : K[X]) : K[X] := C p.leadingCoeff⁻¹ * p

end Gosper.Algorithm
