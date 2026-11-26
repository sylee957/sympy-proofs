module

public import SympyProofs.Calculus.Risch.Spec.Answer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The functions of a complex variable that a tower and an answer stand for. The first
generator is a multiple of the variable, an exponential generator is `Complex.exp` of its
exponent and a logarithm generator is `Complex.log` of its argument, the principal branch.
`integrate_hasDerivAt` says that an answer of `integrate`, read this way, has the integrand
as its derivative at every regular point. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : ℕ}

/-- The values of the generators at the point `z`. A primitive above the first generator
that is not written as a logarithm has no function assigned, and is given the value `0`. -/
noncomputable def Tower.realize : {n : ℕ} → Tower n → ℂ → Fin n → ℂ
  | _, .const, _ => Fin.elim0
  | _, .prim (n := n) t b, z =>
    Fin.lastCases
      (if n = 0 then b.eval (t.realize z) * z
        else match b with
          | .div _ u => Complex.log (u.eval (t.realize z))
          | _ => 0)
      (t.realize z)
  | _, .exp t u, z => Fin.lastCases (Complex.exp (u.eval (t.realize z))) (t.realize z)

/-- The point `z` is regular for the tower: every primitive above the first generator is
written as a logarithm, no denominator in the tower vanishes at `z`, and the argument of
every logarithm lies off the branch cut there. -/
def Tower.RegularAt : {n : ℕ} → Tower n → ℂ → Prop
  | _, .const, _ => True
  | _, .prim (n := n) t b, z =>
    t.RegularAt z ∧ b.Defined (t.realize z) ∧
      (n = 0 ∨ ∃ u, b = .div (t.D u) u ∧ u.eval (t.realize z) ∈ Complex.slitPlane)
  | _, .exp t u, z => t.RegularAt z ∧ u.Defined (t.realize z)

/-- The value of the sum `Σ c log (arg c)` at values `p` of the generators. -/
noncomputable def RootSum.realize (s : RootSum n) (p : Fin n → ℂ) : ℂ :=
  ∑ c ∈ s.roots ℂ, c * Complex.log (s.arg.eval (Fin.lastCases c p))

/-- At values `p` of the generators, the argument of every logarithm of the sum is defined
and lies off the branch cut. -/
def RootSum.RegularAt (s : RootSum n) (p : Fin n → ℂ) : Prop :=
  ∀ c ∈ s.roots ℂ, s.arg.Defined (Fin.lastCases c p : Fin (n + 1) → ℂ) ∧
    s.arg.eval (Fin.lastCases c p) ∈ Complex.slitPlane

/-- The value of an answer at values `p` of the generators. -/
noncomputable def Answer.realize (a : Answer n) (p : Fin n → ℂ) : ℂ :=
  a.field.eval p + (a.sums.map fun s => s.realize p).sum

/-- At values `p` of the generators, every part of the answer is defined and the argument of
every logarithm lies off the branch cut. -/
def Answer.RegularAt (a : Answer n) (p : Fin n → ℂ) : Prop :=
  a.field.Defined p ∧ ∀ s ∈ a.sums, s.RegularAt p

end SympyProofs.Calculus.Risch
