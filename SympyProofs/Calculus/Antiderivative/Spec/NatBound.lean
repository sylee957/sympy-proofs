module

public import SympyProofs.Calculus.Antiderivative.Algebra.NatBound

/-! What the two bounds of a field of constants must satisfy: `LawfulNatBound Γ`. The class
`NatBound Γ` of `Algebra/NatBound.lean` is two functions; this one is two propositions about
them, and only theorems mention it.

A field that is isomorphic to a lawful one, with the bounds computed through the isomorphism
(`NatBound.ofMap`), is lawful: `LawfulNatBound.ofEquiv`. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The two bounds of a field of constants are bounds: a natural number is at most the bound
of the element it is, and a natural number that is a root of a nonzero polynomial is at most
the bound of the polynomial. -/
class LawfulNatBound (Γ : Type) [Field Γ] [DecidableEq Γ] [NatBound Γ] : Prop where
  /-- A natural number is at most the bound of the element it is. -/
  natBound_spec : ∀ (c : Γ) (m : ℕ), c = m → m ≤ NatBound.natBound c
  /-- A natural number that is a root of a nonzero polynomial is at most the bound of the
  polynomial. -/
  natRootBound_spec : ∀ (p : Poly Γ) (m : ℕ), p ≠ 0 → p.eval (m : Γ) = 0 →
    m ≤ NatBound.natRootBound p

variable {Γ Γ' : Type} [Field Γ] [Field Γ'] [DecidableEq Γ] [DecidableEq Γ']

/-- A field isomorphic to a field whose two bounds are bounds, with the bounds computed
through the isomorphism, has bounds that are bounds. -/
theorem LawfulNatBound.ofEquiv [NatBound Γ] [LawfulNatBound Γ] (e : Γ' ≃+* Γ) :
    @LawfulNatBound Γ' _ _ (NatBound.ofMap e) :=
  @LawfulNatBound.mk Γ' _ _ (NatBound.ofMap e)
    (fun c m h => LawfulNatBound.natBound_spec (e c) m (by rw [h, map_natCast]))
    (fun p m hp hroot => LawfulNatBound.natRootBound_spec (p.map e) m
      (Poly.map_ringEquiv_ne_zero e hp)
      (by rw [Poly.eval_natCast_map_ringEquiv, hroot, map_zero]))

end SympyProofs.Calculus.Antiderivative
