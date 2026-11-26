module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Coordinates
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Graph

/-! Return parametric differential solutions over the original tower after adjoining i. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] {n : ℕ}
local notation "E" => WithI (K R 0)

/-- The real and imaginary parts of the parameter vector and the associated field solution. -/
def Trigonometric.Descent.columnParts (v : GraphColumn E n) : GraphColumn R n × GraphColumn R n :=
  let x := project n v.2
  let params := v.1.map (project 0)
  ((params.map QuadraticAlgebra.re, x.re), (params.map QuadraticAlgebra.im, x.im))

/-- Split the whole solution graph through both coordinates of the quadratic extension. -/
def Trigonometric.Descent.solution (width : ℕ) (out : List (K E n) × List (List (K E 0))) :
    List (K R n) × List (List (K R 0)) :=
  let cols := (graphColumns width out.1 out.2).flatMap fun v =>
    let p := columnParts v
    [p.1, p.2]
  describeGraph width cols

end SympyProofs.Calculus.Antiderivative
