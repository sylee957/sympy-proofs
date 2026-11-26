module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Split
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants

/-! Kronecker's rational polynomial factorization algorithm, by interpolation at integers. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Factor

/-- The least common multiple of the coefficient denominators. -/
def denominator : List ℚ → ℕ
  | [] => 1
  | a :: as => a.den.lcm (denominator as)

/-- Clear the coefficient denominators with their least common multiple. -/
def integral (p : Poly ℚ) : Poly ℤ :=
  let d := denominator p.coeffs
  Poly.ofList (p.coeffs.map fun a => a.num * (d / a.den : ℕ))

/-- Positive and negative integer divisors, enumerated in pairs up to the square root. -/
def signedDivisors (v : ℤ) : List ℤ :=
  let a := v.natAbs
  (List.range a.sqrt).flatMap fun k =>
    let b := k + 1
    let c := a / b
    if a % b ≠ 0 then []
    else if b = c then [b, -(b : ℤ)]
    else [b, -(b : ℤ), c, -(c : ℤ)]

/-- The Lagrange basis polynomial for the node i among 0 through m. -/
def basis (m i : ℕ) : Poly ℚ :=
  ∏ j ∈ (Finset.range (m + 1)).erase i, Poly.C ((i : ℚ) - j)⁻¹ * (Poly.X - Poly.C (j : ℚ))

/-- Search the Cartesian product of possible integral values. Stop at the first proper factor. -/
def interpolateFactor (p : Poly ℚ) (q : Poly ℚ) :
    List (Poly ℚ × List ℤ) → Option (Poly ℚ)
  | [] => if proper p q then some q else none
  | (b, vs) :: rest =>
    vs.findSome? fun (v : ℤ) => interpolateFactor p (q + Poly.C (v : ℚ) * b) rest

/-- Look for an integral divisor of degree at most m by its values at m+1 nodes.
A node at which the input vanishes supplies a linear factor directly. -/
def tryDegree (p : Poly ℚ) (z : Poly ℤ) (m : ℕ) : Option (Poly ℚ) :=
  let nodes := List.range (m + 1)
  match nodes.find? (fun (i : ℕ) => z.eval (i : ℤ) == 0) with
  | some i => some (Poly.X - Poly.C (i : ℚ))
  | none => interpolateFactor p 0 (nodes.map fun i => (basis m i, signedDivisors (z.eval (i : ℤ))))

/-- Every reducible polynomial has a factor of degree at most half its degree. -/
def rationalDivisor (p : Poly ℚ) : Option (Poly ℚ) :=
  let z := integral p
  (List.range (p.natDegree / 2)).findSome? fun i => tryDegree p z (i + 1)

end Factor

/-- Monic irreducible factors over the rationals, listed with multiplicity. -/
def factorRational (p : Poly ℚ) : List (Poly ℚ) :=
  Factor.split Factor.rationalDivisor p.natDegree p

/-- Factor rational polynomials by integer interpolation. -/
instance : ConstantFactors ℚ := ⟨factorRational⟩

/-- Transport an executable factorization using coefficient conversion in each direction. -/
@[instance_reducible] def ConstantFactors.ofMaps {F G : Type} [Field F] [Field G]
    [DecidableEq F] [DecidableEq G]
    [ConstantFactors G] (f : F → G) (g : G → F) : ConstantFactors F where
  factors p := (ConstantFactors.factors (p.map f)).map (Poly.map g)

/-- Factor a polynomial over the fraction field of the integers as a rational polynomial. -/
instance : ConstantFactors (K ℤ 0) :=
  ConstantFactors.ofMaps (K.toConstants ℚ) (fun q => (q : K ℤ 0))

/-- Factor a polynomial over the height-zero flat field with the coefficient field's algorithm. -/
instance {F : Type} [Field F] [DecidableEq F] [ConstantFactors F] : ConstantFactors (K F 0) :=
  ConstantFactors.ofMaps (K.toConstants F) K.C

end SympyProofs.Calculus.Antiderivative
