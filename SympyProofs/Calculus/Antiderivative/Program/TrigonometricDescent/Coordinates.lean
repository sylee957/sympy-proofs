module

public import SympyProofs.Calculus.Antiderivative.Program.Trigonometric
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Quadratic

/-! Split a field element over quadratic constants into a pair over the input constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))]
local notation "E" => WithI (K R 0)

/-- Include the original rational function while preserving the generator coordinates. -/
def extendGround : (n : ℕ) → K R n → K E n
  | 0, x => K.C (QuadraticAlgebra.C x : E)
  | n+1, x => substitute (extendGround n) K.gen x

/-- Combine a real and imaginary rational function over the original constants. -/
def assemble (n : ℕ) (z : WithI (K R n)) : K E n :=
  extendGround n z.re + (K.C (WithI.imaginary (K R 0))) * extendGround n z.im

/-- Rationalize a fraction in the imaginary unit, leaving its tower variables untouched. -/
def project : (n : ℕ) → K E n → WithI (K R n)
  | 0, x => K.toConstants E x
  | n+1, x =>
    let (p,q) := x.split
    let phi := fun a => WithI.map (K.lift (R := R)) (project n a)
    let z := (QuadraticAlgebra.C K.gen : WithI (K R (n+1)))
    (p.map phi).eval z / (q.map phi).eval z

/-- Conjugate the constants of a rational function while fixing each original generator. -/
def conjugate (n : ℕ) (x : K E n) : K E n := assemble n (star (project n x))

end SympyProofs.Calculus.Antiderivative.Trigonometric
