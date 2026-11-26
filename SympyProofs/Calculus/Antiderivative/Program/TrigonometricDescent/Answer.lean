module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Coordinates
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Polynomials

/-! Descend logarithmic root sums and elementary answers through a quadratic constant
extension while keeping their original tower variables. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] {n : ℕ}
local notation "E" => WithI (K R 0)

/-- Encode the sum over the two constant embeddings in the original coefficient field.
On shared roots the argument is the product of both conjugate arguments. On a root
belonging to only one embedding the argument is a constant multiple of its own argument. -/
def pairedSums (s : RootSum E n) : List (RootSum R n) :=
  let p := s.modulus.map (fun c => (project 0 c).re)
  let q := s.modulus.map (fun c => (project 0 c).im)
  let a := s.arg.map (fun x => (project n x).re)
  let b := s.arg.map (fun x => (project n x).im)
  let (common,exclusive) := moduli p q
  [⟨common, a^2 + b^2, 1⟩,⟨exclusive, (p.map K.ofConst)*a + (q.map K.ofConst)*b, 1⟩]

/-- Average the two interpretations of a weighted logarithmic sum. -/
def rootSum (s : RootSum E n) : List (RootSum R n) :=
  if s.weight = 0 then [] else pairedSums (halfSum s)

/-- Descend the field part and all logarithmic terms of a restored answer. -/
def answer (a : Answer E n) : Answer R n :=
  ⟨(project n a.field).re, a.sums.flatMap rootSum⟩

/-- Descend an elementary answer or propagate a negative integration decision. -/
def result : Result E n → Result R n
  | .elementary a => .elementary (answer a)
  | .nonelementary => .nonelementary

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
