module

public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite

/-! Exact differentiation of returned logarithmic root sums, without adjoining their roots. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Compute the trace of the logarithmic derivative in the squarefree residue algebra.
A zero modulus or an argument vanishing at a root makes the expression undefined. -/
def RootSum.differentiateAlong (v : List (K R n)) (s : RootSum R n) : Option (K R n) := do
  guard (s.modulus != 0)
  let p := (Step.squarefreeParts s.modulus).1.map (K.ofConst (n := n))
  if p.natDegree = 0 then return 0
  let (a, b) := Step.bezout s.arg p
  guard (s.arg * a + p * b == 1)
  let v := (Poly.X * s.arg.map (K.der v) * a * p.derivative) % p
  return K.ofConst s.weight * v.coeff (p.natDegree - 1) / p.leadingCoeff

/-- Differentiate the field term and each logarithmic root sum using exact field arithmetic. -/
def Answer.differentiateAlong (v : List (K R n)) (a : Answer R n) : Option (K R n) := do
  let logs ← a.sums.mapM (RootSum.differentiateAlong v)
  return K.der v a.field + logs.sum

/-- Differentiate a logarithmic root sum using the velocities of the given tower. -/
def RootSum.differentiate (t : Tower R n) (s : RootSum R n) : Option (K R n) :=
  s.differentiateAlong t.gens

/-- Differentiate an answer using the velocities of the given tower. -/
def Answer.differentiate (t : Tower R n) (a : Answer R n) : Option (K R n) :=
  a.differentiateAlong t.gens

end SympyProofs.Calculus.Antiderivative
