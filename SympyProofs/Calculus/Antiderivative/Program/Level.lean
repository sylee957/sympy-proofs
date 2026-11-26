module

public import SympyProofs.Calculus.Antiderivative.Program.Tower
public import SympyProofs.Calculus.Antiderivative.Algebra.IntegerRelations
public import SympyProofs.Calculus.Antiderivative.Program.Linear
public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Basic

/-! Data returned by one level of integration and the level of the constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- The sum of `c * log (arg c)` over the distinct constant roots of the modulus. -/
structure RootSum (n : ℕ) where
  /-- The polynomial defining the constant roots. -/
  modulus : Poly (K R 0)
  /-- The logarithmic argument as a polynomial in the root. -/
  arg : Poly (K R n)
  /-- Constant multiplying the logarithmic sum as a whole. -/
  weight : K R 0 := 1

/-- A field element and a list of logarithmic root sums. -/
structure Answer (n : ℕ) where
  /-- The part of the primitive in the tower field. -/
  field : K R n
  /-- The logarithmic part of the primitive. -/
  sums : List (RootSum R n)

/-- The outcome of elementary integration. -/
inductive Result (n : ℕ)
  /-- An elementary primitive. -/
  | elementary (answer : Answer R n)
  /-- No elementary primitive exists. -/
  | nonelementary

/-- The integration, parametric solving and logarithmic relation operations at one height. -/
structure Level (n : ℕ) where
  /-- Decide elementary integrability and return a primitive in the affirmative case. -/
  integrate : K R n → Result R n
  /-- Constant vectors spanning the elementary input combinations, each with its primitive. -/
  elementaryBasis : List (K R n) → List (List (K R 0) × Answer R n)
  /-- Return field generators for solutions and homogeneous constraints on their coefficients. -/
  solve : K R n → List (K R n) → List (K R n) × List (List (K R 0))
  /-- Rational constraints for combinations that become logarithmic derivatives after
  multiplication by a positive integer. -/
  logRelations : List (K R n) → List (List ℚ)

/-- At height zero all derivatives vanish, giving the single solution equation
`f * y = Σ cᵢ * gᵢ` and the zero space of logarithmic derivatives. -/
def baseLevel [IntegerRelations (K R 0)] : Level R 0 where
  integrate f := if f = 0 then .elementary ⟨0, []⟩ else .nonelementary
  elementaryBasis gs := (Linear.kernel [gs] gs.length).map fun c => (c, ⟨0, []⟩)
  solve f gs := ([1], [gs.map (- ·) ++ [f]])
  logRelations := IntegerRelations.rows

variable {R}

/-- Regard the same logarithmic sum as a sum over the next tower field. -/
def RootSum.lift {n : ℕ} (s : RootSum R n) : RootSum R (n + 1) :=
  {s with arg := s.arg.map K.lift}

/-- Include the field term and all logarithmic arguments in the next tower field. -/
def Answer.lift {n : ℕ} (a : Answer R n) : Answer R (n + 1) :=
  ⟨K.lift a.field, a.sums.map RootSum.lift⟩

/-- Add a field element to the field part of the primitive. -/
def Answer.addField {n : ℕ} (a : Answer R n) (w : K R n) : Answer R n :=
  ⟨a.field + w, a.sums⟩

/-- Multiply the primitive and each of its logarithm coefficients by a tower constant. -/
def Answer.scale {n : ℕ} (a : Answer R n) (c : K R 0) : Answer R n :=
  ⟨K.ofConst c * a.field, a.sums.map fun s => {s with weight := c * s.weight}⟩

end SympyProofs.Calculus.Antiderivative
