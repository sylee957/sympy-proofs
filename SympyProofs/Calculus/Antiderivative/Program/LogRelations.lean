module

public import SympyProofs.Calculus.Antiderivative.Algebra.IntegerRelations
public import SympyProofs.Calculus.Antiderivative.Program.Coefficients
public import SympyProofs.Calculus.Antiderivative.Program.Step.LogRelations
public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite
public import SympyProofs.Calculus.Antiderivative.Program.Tower

/-! Rational equality constraints for flat fields at any height. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [IntegerRelations (K R 0)] {n : ℕ}

/-- Clear denominators and split coefficients into constant rows, then into rational rows. -/
def rationalRows (xs : List (K R n)) : List (List ℚ) := (rowsOf xs).flatMap IntegerRelations.rows

/-- Rational residue constraints in the newest generator for a supplied factorization. -/
def factoredResidues (ps : List (Poly (K R n))) (ds : Poly (K R n))
    (as : List (Poly (K R n))) : List (List ℚ) :=
  Step.factoredResidueRows rationalRows ps ds as

/-- Data of the common denominator after isolating normal simple poles. -/
structure LogPoleData (F : Type) [Zero F] where
  /-- Squarefree denominator with the special factor removed. -/
  normalDen : Poly F
  /-- The numerators over the squarefree denominator when the pole equations hold. -/
  numerators : List (Poly F)
  /-- Rows enforcing simple normal poles and a constant polynomial part. -/
  poleRows : List (List F)
  /-- The constant terms of the polynomial parts. -/
  constants : List F

/-- Enforce simple normal poles and degree zero at infinity. For an exponential generator,
multiplying the formal derivative by `X` removes the entire power of the special factor. -/
def logPoleData (g : ReducedGen (K R n)) (ws : List (K R (n + 1))) : LogPoleData (K R n) :=
  let (as, q) := commonDen ws
  let d := match g with
    | .prim _ => q.derivative
    | .exp _ => Poly.X * q.derivative
  let repeated := gcd q d
  let s := q / repeated
  let ns := as.map (· / repeated)
  let ps := ns.map (· / s)
  let rows := coefficientSlices (as.map (· % repeated)) ++ (coefficientSlices ps).drop 1
  ⟨s, ns, rows, ps.map (·.coeff 0)⟩

/-- Assemble the logarithmic relation equations using a supplied list of monic irreducible
factors of the normal denominator. The exponential generator contributes one free rational
multiple of its logarithmic derivative to the lower-field equations. -/
def factoredLogStep (D : K R n → K R n) (g : ReducedGen (K R n))
    (lower : List (K R n) → List (List ℚ)) (data : LogPoleData (K R n))
    (factors : List (Poly (K R n))) : List (List ℚ) :=
  let (dx, low) := match g with
    | .prim b => (Poly.C b, lower data.constants)
    | .exp u =>
      let a := D u
      (Poly.C a * Poly.X, Linear.eliminate data.constants.length (lower (data.constants ++ [a])))
  data.poleRows.flatMap rationalRows ++
    factoredResidues factors (Step.polyDer D dx data.normalDen) data.numerators ++ low

end SympyProofs.Calculus.Antiderivative
