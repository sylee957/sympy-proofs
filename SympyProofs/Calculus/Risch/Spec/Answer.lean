module

public import SympyProofs.Calculus.Risch.Program.Answer
public import SympyProofs.Calculus.Risch.Spec.Elementary
public import SympyProofs.Calculus.Risch.Spec.Poly

/-! The meaning of an answer: the derivative it has in the field of a tower. A sum of
logarithms over the roots of a polynomial contributes, for each constant `c` that is a root,
`c` times the logarithmic derivative of the argument at `c`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

theorem constHom_injective (n : ℕ) : Function.Injective (constHom k n) :=
  (constHom k n).injective

namespace RootSum

/-- The values of the generators, with the constant `c` for the root. -/
noncomputable def env (c : k) : Fin (n + 1) → K k n :=
  Fin.lastCases (constHom k n c) (gens k n)

/-- The argument of the logarithm at the root `c`. -/
noncomputable def argAt (s : RootSum n) (c : k) : K k n := s.arg.eval (env k c)

open Classical in
/-- The constants that are roots of the modulus. -/
noncomputable def roots (s : RootSum n) : Finset k :=
  (Poly.model k s.modulus).roots.toFinset.preimage (constHom k n)
    (constHom_injective k n).injOn

/-- The modulus is not zero, and at each root the argument is defined and not zero. -/
def Regular (s : RootSum n) : Prop :=
  Poly.model k s.modulus ≠ 0 ∧ ∀ c ∈ s.roots k, s.arg.Defined (env k c) ∧ s.argAt k c ≠ 0

/-- The derivative of the sum `Σ c log (arg c)`. -/
noncomputable def deriv (t : Tower n) (s : RootSum n) : K k n :=
  ∑ c ∈ s.roots k, constHom k n c * (t.der k (s.argAt k c) / s.argAt k c)

end RootSum

namespace Answer

/-- Every part of the answer is defined in the field. -/
def Regular (a : Answer n) : Prop :=
  Term.InDomain k a.field ∧ ∀ s ∈ a.sums, s.Regular k

/-- The derivative of the answer. -/
noncomputable def deriv (t : Tower n) (a : Answer n) : K k n :=
  t.der k (Term.value k a.field) + (a.sums.map (RootSum.deriv k t)).sum

end Answer

end SympyProofs.Calculus.Risch
