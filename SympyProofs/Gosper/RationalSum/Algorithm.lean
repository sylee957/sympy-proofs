module

public import SympyProofs.Gosper.ShiftlessDecomposition.Algorithm
public import SympyProofs.Gosper.PolynomialSum.Algorithm

/-!
# Parametric rational reduction

`reduce ops P D` accepts a polynomial numerator over any commutative ℚ-algebra
and a fixed rational denominator. Quotients and remainders use Mathlib's monic
division directly. The definition is noncomputable; specialization is justified
by the monicity of the rational divisors, including when numerator degrees drop.
-/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical

/-- A compact sum of translates of a rational fraction. -/
structure ShiftSum (R : Type*) [Semiring R] where
  numerator : Polynomial R
  denominator : Polynomial ℚ
  length : ℕ

/-- Entry `k` is the numerator over `base^(k+1)`. Zero entries are retained. -/
structure Residual (R : Type*) [Semiring R] where
  base : Polynomial ℚ
  numerators : Array (Polynomial R)

structure Result (R : Type*) [Semiring R] where
  polynomial : Polynomial R
  rational : Array (ShiftSum R)
  residual : Array (Residual R)

/-- Invert a rational polynomial modulo a coprime polynomial. The Euclidean
loop tracks only the coefficient of `a`; the other Bézout coefficient is unused.
The final scaling makes the constant gcd equal to one. -/
def inverseMod (a b : Polynomial ℚ) : Polynomial ℚ := Id.run do
  let mut r := a
  let mut previous := b
  let mut u := (1 : Polynomial ℚ)
  let mut previousU := (0 : Polynomial ℚ)
  -- Every nonzero remainder step lowers the degree, so this bound suffices.
  for _ in [:a.natDegree + 1] do
    if r = 0 then break
    let q := previous / r
    let next := previous % r
    let nextU := previousU - q * u
    previous := r
    r := next
    previousU := u
    u := nextU
  return (C previous.leadingCoeff⁻¹ * previousU) % b

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Compute the polynomial primitive, shift-sum certificate, and residual of
`P/D`. Correctness assumes `ops.Valid` and `D ≠ 0`. -/
def reduce (ops : ShiftlessDecomposition.Primitives ℚ)
    (P : Polynomial R) (D : Polynomial ℚ) : Result R := Id.run do
  let groups := ShiftlessDecomposition.decompose ops D
  let monicDenominator := C D.leadingCoeff⁻¹ * D
  let denominator := monicDenominator.map (algebraMap ℚ R)
  let P := C (algebraMap ℚ R D.leadingCoeff⁻¹) * P
  let Q := P /ₘ denominator
  let N := P %ₘ denominator
  let polynomial := PolynomialSum.antidifference Q
  let mut rational : Array (ShiftSum R) := #[]
  let mut residual : Array (Residual R) := #[]
  for group in groups do
    let mut maxMultiplicity : ULift ℕ := ⟨0⟩
    for occurrence in group.occurrences do
      maxMultiplicity := ⟨max maxMultiplicity.down occurrence.multiplicity⟩
    let mut numerators := Array.replicate maxMultiplicity.down (0 : Polynomial R)
    for occurrence in group.occurrences do
      let factor := taylor (occurrence.shift : ℚ) group.base
      let power := factor ^ occurrence.multiplicity
      let complement := monicDenominator / power
      let inverse := inverseMod complement power
      let factorR := factor.map (algebraMap ℚ R)
      let powerR := power.map (algebraMap ℚ R)
      let inverseR := inverse.map (algebraMap ℚ R)
      let mut A := (N * inverseR) %ₘ powerR
      -- Extract base-factor digits from the highest pole order downward.
      for j in [:occurrence.multiplicity] do
        let k := occurrence.multiplicity - j
        let a := A %ₘ factorR
        A := A /ₘ factorR
        let a := taylor ((-occurrence.shift : ℤ) : R) a
        numerators := numerators.modify (k - 1) (· + a)
        if 0 < occurrence.shift then
          rational := rational.push
            { numerator := a
              denominator := group.base ^ k
              length := occurrence.shift.toNat }
    residual := residual.push { base := group.base, numerators := numerators }
  return { polynomial := polynomial, rational := rational, residual := residual }

end Gosper.RationalSum
