module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field

/-! Resultants over the field below a generator, by Euclidean remainder sequences. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

variable {F : Type} [Field F] [DecidableEq F]

/-- Descend the Euclidean remainder sequence, retaining the leading coefficients and signs
in the resultant identity. The second input has degree at most the first. -/
def resultantLoop : ℕ → Poly F → Poly F → F
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    let m := a.natDegree
    let d := b.natDegree
    if d = 0 then b.coeff 0 ^ m
    else
      let r := a % b
      (-1 : F) ^ (m * d) * b.leadingCoeff ^ (m - r.natDegree) * resultantLoop fuel b r

/-- The resultant with both formal degrees chosen to be the input degrees. -/
def resultant (a b : Poly F) : F :=
  if a.natDegree < b.natDegree then
    (-1 : F) ^ (a.natDegree * b.natDegree) * resultantLoop (a.natDegree + 1) b a
  else resultantLoop (b.natDegree + 1) a b

end SympyProofs.Calculus.Antiderivative.Step
