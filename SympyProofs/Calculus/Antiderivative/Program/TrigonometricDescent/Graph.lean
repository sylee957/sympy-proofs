module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Coefficients

/-! Convert between constrained generators and explicit columns of the solution graph. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- A solution column is an input parameter vector together with a field solution. -/
abbrev GraphColumn (R : Type) [CommRing R] [IsDomain R] (n : ℕ) := List (K R 0) × K R n

/-- Compute the joint kernel of the parameter and generator constraints, and evaluate its
solution coordinates using the returned generators. -/
def graphColumns (m : ℕ) (xs : List (K R n)) (rows : List (List (K R 0))) :
    List (GraphColumn R n) :=
  (Linear.kernel rows (m + xs.length)).map fun q => (q.take m, Level.combine (q.drop m) xs)

/-- One row per parameter identifies its value with the corresponding component of a
linear combination of the given solution columns. -/
def describeGraph (m : ℕ) (cols : List (GraphColumn R n)) : List (K R n) × List (List (K R 0)) :=
  (cols.map Prod.snd,
    (List.range m).map fun i => Linear.unit m i ++ cols.map (fun v => -v.1.getD i 0))

end SympyProofs.Calculus.Antiderivative.Trigonometric
