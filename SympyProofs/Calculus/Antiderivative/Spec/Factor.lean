module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor

/-! The factorization needed for the normal poles of a logarithmic derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The factors of a nonzero polynomial are monic and irreducible, and their product
recovers the input with its leading coefficient removed. -/
class LawfulConstantFactors (F : Type) [Field F] [DecidableEq F] [ConstantFactors F] : Prop where
  /-- Each listed factor is monic and irreducible. -/
  irreducible : ∀ p : Poly F, p ≠ 0 → ∀ h ∈ ConstantFactors.factors p,
    (Poly.equiv h).Monic ∧ Irreducible h
  /-- The leading coefficient times the product of the factors equals the input. -/
  product : ∀ p : Poly F, p ≠ 0 →
    Poly.C p.leadingCoeff * (ConstantFactors.factors p).prod = p

end SympyProofs.Calculus.Antiderivative
