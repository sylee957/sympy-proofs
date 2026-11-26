module

public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite
public import SympyProofs.Calculus.Antiderivative.Program.Step.Resultant

/-! Euclidean reduction with a symbolic constant root, splitting a squarefree modulus whenever
a leading coefficient vanishes on only some of its roots. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

variable {F C : Type} [Field F] [DecidableEq F] [Field C] [DecidableEq C]

/-- A polynomial in the tower generator whose coefficients are polynomials in the residue. -/
abbrev BPoly (F : Type) [Field F] [DecidableEq F] := Poly (Poly F)

/-- The common divisor of all coefficient slices, with repeated factors removed. -/
def sliceRoots (rows : List (List C)) : Poly C :=
  let g := rows.foldl (fun g r => gcd g (Poly.ofList r)) 0
  g / gcd g g.derivative

/-- Reduce every coefficient of a polynomial in the tower generator modulo the residue modulus. -/
def reduceMod (m : Poly F) (p : BPoly F) : BPoly F := p.map (· % m)

/-- Remainder in the tower generator, with the divisor monic modulo the residue modulus. -/
def remainderMonic (m : Poly F) (b : BPoly F) : ℕ → BPoly F → BPoly F
  | 0, a => a
  | fuel + 1, a =>
    if a = 0 || a.natDegree < b.natDegree then a
    else
      let q := Poly.monomial (a.natDegree - b.natDegree) a.leadingCoeff
      remainderMonic m b fuel (reduceMod m (a - q * b))

/-- Split a squarefree constant modulus into pieces where the polynomial has constant degree,
and make every nonzero polynomial monic on its piece. -/
def monicPieces (embed : C → F) (constantRoots : Poly F → Poly C) :
    ℕ → Poly C → BPoly F → List (Poly C × BPoly F)
  | 0, m, p => [(m, reduceMod (m.map embed) p)]
  | fuel + 1, m, p =>
    let mF := m.map embed
    let p := reduceMod mF p
    if p = 0 then [(m, 0)]
    else
      let l := p.leadingCoeff
      let bad := gcd m (constantRoots l)
      if bad.natDegree = 0 then
        let inv := (bezout l mF).1
        [(m, reduceMod mF (Poly.C inv * p))]
      else
        monicPieces embed constantRoots fuel bad p ++
          monicPieces embed constantRoots fuel (m / bad) p

/-- A common divisor in the generator for every specialization of the residue to a root of
the squarefree constant modulus. -/
def gcdAtRoots (embed : C → F) (constantRoots : Poly F → Poly C) :
    ℕ → Poly C → BPoly F → BPoly F → List (Poly C × BPoly F)
  | 0, m, a, _ => monicPieces embed constantRoots (m.natDegree + 1) m a
  | fuel + 1, m, a, b =>
    (monicPieces embed constantRoots (m.natDegree + 1) m b).flatMap fun (h, d) =>
      if d = 0 then monicPieces embed constantRoots (h.natDegree + 1) h a
      else
        let hF := h.map embed
        let a := reduceMod hF a
        let r := remainderMonic hF d (a.natDegree + 1) a
        gcdAtRoots embed constantRoots fuel h d r

/-- Lift a polynomial into the bivariate ring, making its coefficients independent of the root. -/
def independent (p : Poly F) : BPoly F := p.map Poly.C

/-- The numerator minus the symbolic residue times the derivative of the denominator. -/
def shifted (a e : Poly F) : BPoly F :=
  independent a - Poly.C Poly.X * independent e

end SympyProofs.Calculus.Antiderivative.Step
