module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Rational
public import SympyProofs.Calculus.Antiderivative.Algebra.IntegerRelations
import Mathlib.Tactic.Linarith

/-! The Gaussian rational constants, with exact arithmetic on rational real and imaginary parts. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Adjoin an imaginary unit to a field where negative one is a nonsquare. -/
abbrev WithI (F : Type) [Field F] := QuadraticAlgebra F (-1) 0

/-- The field of pairs of rational numbers with i² = −1. -/
abbrev Gaussian := WithI ℚ

instance : Fact (∀ x : ℚ, x ^ 2 ≠ -1 + 0 * x) := ⟨fun x h => by nlinarith [sq_nonneg x]⟩

namespace Gaussian

/-- The imaginary unit in the rational quadratic field. -/
def I : Gaussian := ⟨0, 1⟩

/-- The imaginary unit squares to negative one. -/
theorem I_sq : I ^ 2 = -1 := by
  ext <;> norm_num [I, pow_two]

end Gaussian

namespace WithI

variable {F : Type} [Field F] [DecidableEq F]
variable [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)]
local notation "G" => WithI F

/-- The canonical square root of negative one in the extended coefficient field. -/
def imaginary (F : Type) [Field F] : WithI F := ⟨0, 1⟩

omit [DecidableEq F] [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)] in
/-- The element with imaginary part one squares to negative one. -/
theorem imaginary_sq : imaginary F ^ 2 = -1 := by ext <;> norm_num [imaginary, pow_two]

/-- A natural root is a root of either nonzero rational coefficient projection. -/
instance [NatBound F] : NatBound G where
  natBound z := NatBound.natBound z.re
  natRootBound p :=
    let re := p.map QuadraticAlgebra.re
    NatBound.natRootBound (if re = 0 then p.map QuadraticAlgebra.im else re)

/-- A rational relation is the simultaneous vanishing of its real and imaginary parts. -/
instance [IntegerRelations F] : IntegerRelations G where
  rows zs := IntegerRelations.rows (zs.map QuadraticAlgebra.re) ++
    IntegerRelations.rows (zs.map QuadraticAlgebra.im)

/-- Translate the polynomial by a constant, using Horner evaluation. -/
def translate (p : Poly G) (a : G) : Poly G :=
  p.coeffs.foldr (fun c q => Poly.C c + (Poly.X + Poly.C a) * q) 0

/-- The product with the conjugate has coefficients in the original field. -/
def normPoly (p : Poly G) : Poly F :=
  (p * p.map star).map QuadraticAlgebra.re

/-- Normalize and choose a shift making the coefficient below the leading term nonreal. -/
def shift (p : Poly G) : G :=
  if (p.coeff (p.natDegree - 1)).im = 0 then imaginary F else 0

/-- A factor of the norm contributes its gcd with the translated input. -/
def normDivisor [ConstantFactors F] (p : Poly G) : Option (Poly G) :=
  let m := normalize p
  let a := shift m
  let q := translate m a
  (ConstantFactors.factors (normPoly q)).findSome? fun h =>
    let f := translate (gcd q (h.map (algebraMap F G))) (-a)
    if Factor.proper p f then some f else none

/-- Repeated factors are split off first. One norm in a suitable translate handles the rest. -/
def divisor [ConstantFactors F] (p : Poly G) : Option (Poly G) :=
  let g := gcd p p.derivative
  if Factor.proper p g then some g else normDivisor p

/-- Factor polynomials over the quadratic extension by a shift and norm. -/
instance [ConstantFactors F] : ConstantFactors G := ⟨fun p => Factor.split divisor p.natDegree p⟩

end WithI

end SympyProofs.Calculus.Antiderivative
