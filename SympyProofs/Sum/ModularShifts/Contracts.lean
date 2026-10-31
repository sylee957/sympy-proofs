module

public import SympyProofs.Sum.ModularShifts.Algorithm

/-!
# Contracts for integer resultants, finite-field factorization, and Hensel lifting

A single prime and precision must be used for both inputs. At that prime, good
reduction is preserved by monic divisors and integer translations. Unique monic
Hensel factors then respect divisibility and translation. We expose those
standard compatibility properties explicitly as part of the supplied lifting
contract; their derivation from a particular Hensel implementation is not proved
here. In particular, no contract assumes a list of shifts or completeness of the
centered-factor matching algorithm.

The predicate `Good` describes the polynomials admissible at the chosen prime
(including the degree restriction). It is only a proof witness, never a runtime
argument. Rational inputs are monic and square-free. Their primitive integer
representatives are prepared once and shared by reduction and Hensel lifting.
-/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

/-- The supplied resultant agrees with the mathematical resultant whenever
at least one input is nonconstant. Constant inputs are handled directly by `shifts`. -/
def ResultantValid (ops : Backend) : Prop :=
  ∀ P Q, P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0 → ops.resultant P Q = P.resultant Q

/-- The excluded integer for the nonconstant inputs reaching prime selection. -/
def excludedDivisors (ops : Backend) (P : Polynomial ℤ) : ℕ :=
  P.leadingCoeff.natAbs * (ops.resultant P P.derivative).natAbs

/-- The integer leading coefficient survives and the reduction is separable. -/
def GoodIntegerReduction (r : ℕ) (P : Polynomial ℤ) : Prop :=
  (P.leadingCoeff : ZMod r) ≠ 0 ∧ (P.map (Int.castRingHom (ZMod r))).Separable

/-- The factor array associated with an input, used to state the backend laws.
`shifts` performs these operations on its cached primitive integer input. -/
def factors (ops : Backend) (r e : ℕ) (p : Polynomial ℚ) :
    Array (Polynomial (ZMod (r ^ e))) :=
  let P := (clearDenominators p).primPart
  ops.henselLift r e P (ops.factorMod r (reduce r P))

/-- The primitive integer input has a nonzero leading coefficient and separable
reduction at the prime. Prime selection verifies these conditions for both inputs. -/
def GoodReduction (r : ℕ) (p : Polynomial ℚ) : Prop :=
  GoodIntegerReduction r (clearDenominators p).primPart

/-- The finite-field operation returns a complete monic irreducible factorization
when called on a monic square-free polynomial. -/
def FactorModValid (ops : Backend) : Prop :=
  ∀ (r : ℕ), r.Prime → ∀ p : Polynomial (ZMod r), p.Monic → Squarefree p →
    (ops.factorMod r p).toList.prod = p ∧
    ∀ f ∈ ops.factorMod r p, f.Monic ∧ Irreducible f

/-- Factorization and unique-lifting laws on the good-reduction domain. These are
requirements on the supplied backend, rather than properties checked at runtime. -/
structure FactorizationLaws (ops : Backend) (r e : ℕ)
    (Good : Polynomial ℚ → Prop) : Prop where
  divisor_good : ∀ {p d}, Good p → d.Monic → d ∣ p → Good d
  translate_good : ∀ {p}, Good p → ∀ h : ℤ, Good (taylor (h : ℚ) p)
  nonempty : ∀ {p}, Good p → 0 < p.natDegree → (factors ops r e p).toList ≠ []
  monic : ∀ {p}, Good p → ∀ f ∈ factors ops r e p, f.Monic
  positive_degree : ∀ {p}, Good p → ∀ f ∈ factors ops r e p, 0 < f.natDegree
  degree_unit : ∀ {p}, Good p → ∀ f ∈ factors ops r e p,
    IsUnit (f.natDegree : ZMod (r ^ e))
  divides : ∀ {p d}, Good p → d.Monic → d ∣ p →
    ∀ f ∈ factors ops r e d, f ∈ factors ops r e p
  translate : ∀ {p}, Good p → ∀ h : ℤ, ∀ f ∈ factors ops r e p,
    taylor (h : ZMod (r ^ e)) f ∈ factors ops r e (taylor (h : ℚ) p)
  reconstruct : ∀ {p}, Good p →
    (factors ops r e p).toList.prod = reduce (r ^ e) (clearDenominators p).primPart

structure Backend.Valid (ops : Backend) : Prop where
  resultant_valid : ResultantValid ops
  factorMod_valid : FactorModValid ops
  lifting_valid : ∀ (p q : Polynomial ℚ) (r e : ℕ),
    p.Monic → q.Monic → Squarefree p → Squarefree q →
    r.Prime → 0 < e → max p.natDegree q.natDegree < r →
    GoodReduction r p → GoodReduction r q →
    ∃ Good, Good p ∧ Good q ∧ FactorizationLaws ops r e Good

end Gosper.ModularShifts
