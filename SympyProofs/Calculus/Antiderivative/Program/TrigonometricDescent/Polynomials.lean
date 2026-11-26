module

public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite

/-! Polynomials for averaging logarithmic root sums across a quadratic extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute a scalar multiple of the root parameter in a polynomial. -/
def rescale (a : F) (p : Poly F) : Poly F :=
  p.coeffs.foldr (fun b q => Poly.C b + (Poly.C a * Poly.X) * q) 0

/-- Replace a weighted residue c by w*c/2, so the rescaled root sum contributes half
of the original derivative with unit weight. -/
def halfSum {S : Type} [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S]
    [Div S] {n : ℕ} (s : RootSum S n) : RootSum S n :=
  let a := 2 / s.weight
  ⟨rescale a s.modulus, rescale (K.ofConst a) s.arg, 1⟩

/-- Root sets common to both conjugate moduli and exclusive to either one. -/
def moduli (p q : Poly F) : Poly F × Poly F :=
  let common := gcd p q
  let union := (Step.squarefreeParts (p^2 + q^2)).1
  (common,union / gcd union common)

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
