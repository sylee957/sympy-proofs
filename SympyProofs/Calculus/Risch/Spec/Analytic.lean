module

public import SympyProofs.Calculus.Risch.Spec.Answer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The functions of a complex variable that a tower and an answer stand for. The first
generator is a multiple of the variable, an exponential generator is `Complex.exp` of its
exponent and a logarithm generator is `Complex.log` of its argument, the principal branch.
`integrate_hasDerivAt` says that an answer of `integrate`, read this way, has the integrand
as its derivative at every regular point.

No branch has to be chosen. `integrate_hasDerivAt_of_solution` says the same for any
functions that satisfy the differential equations of the tower (`Tower.SolvedBy`) and any
continuous logarithms of the arguments in the answer (`Answer.HasLogs`), at every point
where no denominator vanishes. The converse, `integrate_no_function_of_solution`, holds for
such functions as well, when no exponential generator vanishes (`Tower.ExpNonzero`). -/

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

/-! ### Without a choice of branches -/

/-- At `z`, the functions `g` are defined in the tower and satisfy its differential
equations: the derivative of each is the value of the derivative of its generator. -/
def Tower.SolvedBy (t : Tower n) (g : ℂ → Fin n → ℂ) (z : ℂ) : Prop :=
  ∀ i, (t.vel i).Defined (g z) ∧ HasDerivAt (fun w => g w i) ((t.vel i).eval (g z)) z

/-- At values `p` of the generators, no exponential generator vanishes. A solution of
`θ′ = u′ θ` may be identically zero, and then it is not an exponential. -/
def Tower.ExpNonzero : {n : ℕ} → Tower n → (Fin n → ℂ) → Prop
  | _, .const, _ => True
  | _, .prim t _, p => t.ExpNonzero fun i => p i.castSucc
  | _, .exp (n := n) t _, p => (t.ExpNonzero fun i => p i.castSucc) ∧ p (Fin.last n) ≠ 0

/-- The value of an answer at values `p` of the generators, where `ℓ s c` is the value of
the logarithm of the sum `s` at the root `c`. -/
noncomputable def Answer.realizeWith (a : Answer n) (ℓ : RootSum n → ℂ → ℂ)
    (p : Fin n → ℂ) : ℂ :=
  a.field.eval p + (a.sums.map fun s => ∑ c ∈ s.roots ℂ, c * ℓ s c).sum

/-- Near `z`, each function `ℓ s c` is a continuous logarithm of the argument of the sum `s`
at the root `c`, along the functions `g`: the argument is defined at `z`, and
`exp (ℓ s c w)` is the argument at `g w` for `w` near `z`. -/
def Answer.HasLogs (a : Answer n) (ℓ : RootSum n → ℂ → ℂ → ℂ) (g : ℂ → Fin n → ℂ)
    (z : ℂ) : Prop :=
  ∀ s ∈ a.sums, ∀ c ∈ s.roots ℂ,
    s.arg.Defined (Fin.lastCases c (g z) : Fin (n + 1) → ℂ) ∧ ContinuousAt (ℓ s c) z ∧
      ∀ᶠ w in nhds z, Complex.exp (ℓ s c w) = s.arg.eval (Fin.lastCases c (g w))

/-- At values `p` of the generators, no denominator of the answer vanishes and no argument
of a logarithm vanishes. -/
def Answer.NonsingularAt (a : Answer n) (p : Fin n → ℂ) : Prop :=
  a.field.Defined p ∧ ∀ s ∈ a.sums, ∀ c ∈ s.roots ℂ,
    s.arg.Defined (Fin.lastCases c p : Fin (n + 1) → ℂ) ∧ s.arg.eval (Fin.lastCases c p) ≠ 0

end SympyProofs.Calculus.Risch
