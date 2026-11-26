module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field

/-! Hermite reduction over a differential field, in its newest indeterminate. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

variable {F : Type} [Field F] [DecidableEq F]

/-- Differentiate the coefficients and apply the chain rule to the indeterminate. -/
def polyDer (D : F → F) (dx p : Poly F) : Poly F := p.map D + dx * p.derivative

/-- The radical of a nonzero denominator and its repeated part in characteristic zero. -/
def squarefreeParts (q : Poly F) : Poly F × Poly F :=
  let repeated := gcd q q.derivative
  (q / repeated, repeated)

/-- The monic Bézout coefficients from a single pass of the extended Euclidean algorithm. -/
def bezout (a b : Poly F) : Poly F × Poly F :=
  let (g, s, t) := EuclideanDomain.xgcdAux a 1 0 b 0 1
  let u := Poly.C g.leadingCoeff⁻¹
  (u * s, u * t)

/-- The fraction with normal denominator and the numerator over the special power. -/
structure PoleParts (F : Type) [Zero F] where
  /-- The numerator handed to Hermite reduction. -/
  normalNum : Poly F
  /-- The factors of the denominator other than the given power of the indeterminate. -/
  normalDen : Poly F
  /-- The numerator over the given power of the indeterminate. -/
  specialNum : Poly F

/-- Separate the full power `X^k` dividing the denominator by a Bézout decomposition. -/
def separatePole (a q : Poly F) (k : ℕ) : PoleParts F :=
  if k = 0 then ⟨a, q, 0⟩
  else
    let special := Poly.X ^ k
    let normal := q / special
    let (s, t) := bezout special normal
    ⟨a * s, normal, a * t⟩

/-- The numerator of an exact derivative and the remaining numerator and repeated denominator. -/
structure HermiteStep (F : Type) [Zero F] where
  /-- The extracted rational function has this numerator and the old repeated denominator. -/
  exactNum : Poly F
  /-- The numerator after extracting the derivative. -/
  numerator : Poly F
  /-- The new repeated denominator, of smaller degree. -/
  repeated : Poly F

/-- Remove one layer of repeated normal factors from `a / (s * m)`. -/
def hermiteStep (D : F → F) (dx s a m : Poly F) : HermiteStep F :=
  let (rad, m') := squarefreeParts m
  let e := -((s * polyDer D dx m) / m)
  let (b, c) := bezout e rad
  let exactNum := a * b
  ⟨exactNum, a * c - polyDer D dx exactNum * (s / rad), m'⟩

/-- A sum of exact rational terms and a remaining fraction. -/
structure Reduction (F : Type) [Zero F] where
  /-- Pairs of polynomials giving the rational terms whose derivatives were removed. -/
  exactTerms : List (Poly F × Poly F)
  /-- The numerator of the remaining fraction. -/
  numerator : Poly F
  /-- Its denominator, squarefree on a normal input. -/
  denominator : Poly F

/-- Peel off repeated factors, returning every exact term and the remaining fraction. -/
def hermiteLoop (D : F → F) (dx s : Poly F) : ℕ → Poly F → Poly F → Reduction F
  | 0, a, m => ⟨[], a, s * m⟩
  | fuel + 1, a, m =>
    if m.natDegree = 0 then ⟨[], a, s * m⟩
    else
      let next := hermiteStep D dx s a m
      let tail := hermiteLoop D dx s fuel next.numerator next.repeated
      { tail with exactTerms := (next.exactNum, m) :: tail.exactTerms }

/-- Reduce a fraction whose denominator has only normal factors. -/
def hermite (D : F → F) (dx a q : Poly F) : Reduction F :=
  if q = 0 then ⟨[], 0, 1⟩
  else
    let (s, m) := squarefreeParts q
    hermiteLoop D dx s m.natDegree a m

end SympyProofs.Calculus.Antiderivative.Step
