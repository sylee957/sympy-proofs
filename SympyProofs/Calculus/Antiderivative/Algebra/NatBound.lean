module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Basic

/-! The bounds on natural numbers that the algorithm asks of a field of constants, beyond its
arithmetic. The degree of a solution at a primitive step and the exponents at an exponential
step are natural numbers determined by equations over the constants: such a number is either
a constant itself, or a root of a polynomial with constant coefficients. `NatBound Γ` gives a
bound in each case.

The class is data only: two functions. What they must satisfy is the class of propositions
`LawfulNatBound` of `Spec/NatBound.lean`, which only theorems mention, as `LawfulBEq` is to
`BEq`.

A type that is mapped into one with the bounds has two such functions too, computed through
the map: `NatBound.ofMap`. The map is a plain function. When it is an isomorphism of fields
and the bounds of the target are bounds, so are these (`LawfulNatBound.ofEquiv`). -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Bounds on natural numbers in a field of constants. -/
class NatBound (Γ : Type) [Zero Γ] where
  /-- An upper bound for the natural number the element is, if it is one. -/
  natBound : Γ → ℕ
  /-- An upper bound for the natural numbers that are roots of a nonzero polynomial. -/
  natRootBound : Poly Γ → ℕ

/-- The two bounds computed through a map into a type that has them: the bound of an element
is the bound of its image, and the bound of a polynomial is the bound of the polynomial of the
images of its coefficients. -/
@[instance_reducible] def NatBound.ofMap {Γ Γ' : Type} [Zero Γ] [Zero Γ'] [DecidableEq Γ]
    [DecidableEq Γ'] [NatBound Γ] (e : Γ' → Γ) : NatBound Γ' where
  natBound c := NatBound.natBound (e c)
  natRootBound p := NatBound.natRootBound (p.map e)

end SympyProofs.Calculus.Antiderivative
