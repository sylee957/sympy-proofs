module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Tan
public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split

/-! Rational changes of variable for native tangent inputs and their answers. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R S : Type} [CommRing R] [IsDomain R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

namespace Trigonometric

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Evaluate the canonical fraction in the chosen newest generator, mapping its coefficients
through the already compiled lower field. -/
def substitute (lower : K R n → K S n) (z : K S (n+1)) (f : K R (n+1)) : K S (n+1) :=
  let (p,q) := f.split
  let phi := fun a => K.lift (lower a)
  (p.map phi).eval z / (q.map phi).eval z

end Trigonometric

open Trigonometric

/-- Replace each auxiliary exponential by its rational expression in the corresponding
original tangent, recursively transforming all lower coefficients. -/
def Tower.restore (i : K S 0) : {m : ℕ} → Tower R m → K S m → K S m
  | _, .base => id
  | _, .step t g =>
    match g with
    | .prim _ | .exp _ => substitute (t.restore i) K.gen
    | .tan _ => substitute (t.restore i) (Kind.Tan.exponential i K.gen)

/-- Express each coefficient of a logarithmic argument in the original coordinates. -/
def Tower.restoreSum (t : Tower R n) (i : K S 0) (s : RootSum S n) : RootSum S n :=
  {s with arg := s.arg.map (t.restore i)}

/-- Express the entire primitive, including logarithmic arguments, in original coordinates. -/
def Tower.restoreAnswer (t : Tower R n) (i : K S 0) (a : Answer S n) : Answer S n :=
  ⟨t.restore i a.field, a.sums.map (t.restoreSum i)⟩

/-- Express the primitive in original coordinates whenever elementary integration succeeds. -/
def Tower.restoreResult (t : Tower R n) (i : K S 0) : Result S n → Result S n
  | .elementary a => .elementary (t.restoreAnswer i a)
  | .nonelementary => .nonelementary

end SympyProofs.Calculus.Antiderivative
