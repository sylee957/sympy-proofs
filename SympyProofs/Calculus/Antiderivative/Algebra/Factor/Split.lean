module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field

/-! Splitting a polynomial recursively at proper divisors. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {F : Type} [Field F] [DecidableEq F]

/-- A nonconstant proper divisor, up to a scalar multiple. -/
def proper (p b : Poly F) : Bool :=
  0 < b.natDegree && b.natDegree < p.natDegree && p % b == 0

/-- Split the two factors recursively after checking their product. Normalizing each leaf
removes any scalar multiple introduced by a divisor search. -/
def split (find : Poly F → Option (Poly F)) : ℕ → Poly F → List (Poly F)
  | 0, p => if p.natDegree = 0 then [] else [normalize p]
  | fuel + 1, p =>
    if p.natDegree = 0 then []
    else if p.natDegree = 1 then [normalize p]
    else match find p with
      | none => [normalize p]
      | some b =>
        let q := p / b
        if 0 < b.natDegree ∧ 0 < q.natDegree ∧ b * q = p then
          split find fuel b ++ split find fuel q
        else [normalize p]

end SympyProofs.Calculus.Antiderivative.Factor
