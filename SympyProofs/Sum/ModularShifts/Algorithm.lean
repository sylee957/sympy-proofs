module

public import SympyProofs.Sum.ModularShifts.PrimeSearch

/-!
# Modular dispersion sets (Gerhard–Giesbrecht–Storjohann–Zima, §6)

The algorithm clears denominators once per input and uses integer derivative
resultants to choose a prime giving square-free reduction. The supplied backend
computes these resultants, factors over the finite field, and Hensel-lifts the
integer inputs. `shifts` centers the lifted factors, matches pairs, reconstructs
signed integers, and filters with exact integer gcds. Shift enumeration uses
centered factors without constructing a bivariate shift resultant.

The convention here is `gcd(p(x), q(x+h))`, opposite to the paper's first argument
being shifted. Thus the candidate is `(nextCoeff f - nextCoeff g) / degree f`.
-/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

/-- The least common multiple of all coefficient denominators. -/
def commonDenominator (p : Polynomial ℚ) : ℕ :=
  p.support.lcm fun i => (p.coeff i).den

/-- Multiply by one common denominator, producing integer coefficients. -/
def clearDenominators (p : Polynomial ℚ) : Polynomial ℤ :=
  let d := commonDenominator p
  p.sum fun i a => monomial i (a.num * (d / a.den : ℕ))

/-- A rational root-radius bound, also defined for constant and zero polynomials. -/
def radius (p : Polynomial ℚ) : ℚ :=
  1 + (∑ i ∈ Finset.range p.natDegree, |p.coeff i|) / |p.leadingCoeff|

/-- Monic reduction of an integer polynomial; the selected prime avoids its
leading coefficient, so that coefficient is invertible modulo every lifting power. -/
def reduce (m : ℕ) (P : Polynomial ℤ) : Polynomial (ZMod m) :=
  C (P.leadingCoeff : ZMod m)⁻¹ * P.map (Int.castRingHom (ZMod m))

structure Backend where
  resultant : Polynomial ℤ → Polynomial ℤ → ℤ
  factorMod : (prime : ℕ) → Polynomial (ZMod prime) → Array (Polynomial (ZMod prime))
  henselLift : (prime exponent : ℕ) → Polynomial ℤ →
    Array (Polynomial (ZMod prime)) → Array (Polynomial (ZMod (prime ^ exponent)))

/-- The coefficient of degree `d-1` divided by `d`; the prime exceeds `d`. -/
def mean {m : ℕ} (f : Polynomial (ZMod m)) : ZMod m :=
  f.nextCoeff * (f.natDegree : ZMod m)⁻¹

/-- A monic factor translated to have zero coefficient in degree `d-1`. -/
def center {m : ℕ} (f : Polynomial (ZMod m)) : Polynomial (ZMod m) :=
  taylor (-mean f) f

/-- Integer shifts for monic square-free inputs. These preconditions and the
backend contracts appear only in the correctness theorem. -/
def shifts (ops : Backend) (p q : Polynomial ℚ) : Array ℤ := Id.run do
  if p.natDegree = 0 ∨ q.natDegree = 0 then return #[]
  let B := ⌈radius p + radius q⌉₊
  let P := (clearDenominators p).primPart
  let Q := (clearDenominators q).primPart
  -- Compute each derivative resultant once; prime selection uses integer divisibility.
  let c := ops.resultant P P.derivative
  let badP := P.leadingCoeff.natAbs * c.natAbs
  let c := ops.resultant Q Q.derivative
  let badQ := Q.leadingCoeff.natAbs * c.natAbs
  let lower := max p.natDegree q.natDegree
  let bad := max 1 (badP * badQ)
  let mut r := lower + 1
  for candidate in [lower + 1:2 * max lower bad + 1] do
    if candidate.Prime ∧ ¬candidate ∣ bad then
      r := candidate
      break
  let e := Nat.log r (2 * B) + 1
  let fs := ops.factorMod r (reduce r P)
  let fs := ops.henselLift r e P fs
  let gs := ops.factorMod r (reduce r Q)
  let gs := ops.henselLift r e Q gs
  -- Match centered factors and verify each signed candidate using the integer inputs.
  let mut found := #[]
  for f in fs do
    let cf := center f
    for g in gs do
      if f.natDegree = g.natDegree ∧ cf = center g then
        let h := ((f.nextCoeff - g.nextCoeff) * (f.natDegree : ZMod (r ^ e))⁻¹).valMinAbs
        if 0 < (GCDMonoid.gcd P (taylor h Q)).natDegree ∧ h ∉ found then
          found := found.push h
  return found

end Gosper.ModularShifts
