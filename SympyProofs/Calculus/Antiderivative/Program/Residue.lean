module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Recognize
public import SympyProofs.Calculus.Antiderivative.Program.Coefficients
public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Program.Step.Residue

/-! The Rothstein–Trager logarithmic part of a proper fraction with squarefree normal denominator.
The extra variable in the resultant is a constant parameter, independent of the tower generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- The squarefree polynomial cutting out the constant roots in every constant extension. -/
def constantRoots (p : Poly (K R n)) : Poly (K R 0) := Step.sliceRoots (rowsOf p.coeffs)

/-- The resultant of `d` and `a - z e`, expanded in the constant parameter `z`. -/
def residuePolynomial (a d e : Poly (K R n)) : Poly (K R n) :=
  let r := Step.resultant (d.map K.lift) (a.map K.lift - Poly.C K.gen * e.map K.lift)
  (K.split r).1

/-- Exchange the two polynomial variables, evaluating the tower variable at its generator. -/
def argument (d : Step.BPoly (K R n)) : Poly (K R (n + 1)) :=
  d.coeffs.foldr (fun c p => c.map K.lift + Poly.C K.gen * p) 0

/-- The roots on one modulus piece share the same degree of their gcd logarithmic argument. -/
def rootSum (piece : Poly (K R 0) × Step.BPoly (K R n)) : RootSum R (n + 1) :=
  { modulus := piece.1, arg := argument piece.2 }

/-- The negative sum of the roots of a modulus, weighted by the common argument degree. -/
def correction (piece : Poly (K R 0) × Step.BPoly (K R n)) : K R 0 :=
  let m := piece.1
  (piece.2.natDegree : K R 0) * (m.coeff (m.natDegree - 1) / m.leadingCoeff)

/-- A single constant residue gives a logarithm of the whole denominator. The constant
quotient of its derivative accounts for the polynomial part of that logarithmic derivative. -/
def uniformPart (a d e : Poly (K R n)) : Option (List (RootSum R (n + 1)) × K R n) := do
  let (q, r) := e.divMod d
  if r = 0 || a.natDegree != r.natDegree || q.natDegree != 0 then none
  else
    let c := (K.const? (a.leadingCoeff / r.leadingCoeff)).getD 0
    let v : K R n := K.ofConst c
    if Poly.C v * r = a then
      let s : RootSum R (n + 1) := ⟨Poly.X - Poly.C c, Poly.C (K.joinPoly d), 1⟩
      some ([s], -(v * q.coeff 0))
    else none

/-- Run the bivariate Euclidean algorithm over the constant roots of the resultant. -/
def rawPieces (a d e : Poly (K R n)) : List (Poly (K R 0) × Step.BPoly (K R n)) :=
  let r := constantRoots (residuePolynomial a d e)
  if r.natDegree = 0 then [] else
    Step.gcdAtRoots K.ofConst constantRoots (d.natDegree + 2) r
      (Step.shifted a e) (Step.independent d)

/-- Logarithmic root sums and a lower-field correction, or failure of the residue criterion.
Here `e` is the derivative of the denominator, and `twist` is the linear coefficient of
the generator velocity. -/
def logPart (a d e : Poly (K R n)) (twist : K R n) :
    Option (List (RootSum R (n + 1)) × K R n) :=
  if a = 0 || d.natDegree = 0 then some ([], 0)
  else if let some answer := uniformPart a d e then some answer
  else
    let pieces := (rawPieces a d e).filter fun p => p.2.natDegree != 0
    let accounted := (pieces.map fun p => p.1.natDegree * p.2.natDegree).sum
    if accounted = d.natDegree then
      some (pieces.map rootSum, twist * K.ofConst (pieces.map correction).sum)
    else none

end SympyProofs.Calculus.Antiderivative.Residue
