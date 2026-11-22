module

public import SympyProofs.CubicEquation.CardanoReal.ReIm.Properties
public import SympyProofs.CubicEquation.CardanoReal.KnownRoot

/-!
# Cardano's modified-principal formula with real and imaginary parts

For real depressed coefficients `p,q`, form the sum `W` of the two principal
cube roots. Then `r = W.re - sqrt(3) * W.im` is a real root. Factoring out
`x - r` gives the other two roots as `(-r ± sqrt(-3*r^2 - 4*p)) / 2`.

`modifiedPrincipalCubicRootsReIm a b c d` computes the three solutions of the
real cubic `a*x^3 + b*x^2 + c*x + d = 0` this way, as a `CardanoRootsReIm`
structure whose first field is a real number.
It uses no modified-root function, conjugation, roots of unity, conditionals,
or division by radicals. Both square roots are complex principal square roots,
so the other two solutions may be nonreal.

`cardano_formula_modifiedPrincipal_re_im` states that for `a ≠ 0` its three
fields are exactly the solutions, including repeated and triple roots.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- Three solutions of a real cubic, the first of them a real number. -/
structure CardanoRootsReIm where
  x₀ : ℝ
  x₁ : ℂ
  x₂ : ℂ

/-- The three Cardano solutions of the real cubic `a*x^3 + b*x^2 + c*x + d = 0`,
using principal cube roots and real and imaginary parts. The first solution is
a real number; the other two come from the quadratic that remains after
dividing by it, and are allowed to be nonreal. -/
def modifiedPrincipalCubicRootsReIm (a b c d : ℝ) : CardanoRootsReIm :=
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
  let s := Complex.sqrt (Δ : ℂ)
  let W := principal (-(q : ℂ) / 2 + s) + principal (-(q : ℂ) / 2 - s)
  let r : ℝ := W.re - Real.sqrt 3 * W.im
  let t := Complex.sqrt (-3 * (r : ℂ) ^ 2 - 4 * (p : ℂ))
  let shift : ℝ := (b / a) / 3
  { x₀ := r - shift
    x₁ := (-(r : ℂ) + t) / 2 - (shift : ℂ)
    x₂ := (-(r : ℂ) - t) / 2 - (shift : ℂ) }

/-- For every real cubic with nonzero leading coefficient, the three fields are
exactly its complex solutions. -/
theorem cardano_formula_modifiedPrincipal_re_im {a : ℝ} (ha : a ≠ 0)
    (b c d : ℝ) (x : ℂ) :
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = ((modifiedPrincipalCubicRootsReIm a b c d).x₀ : ℂ) ∨
      x = (modifiedPrincipalCubicRootsReIm a b c d).x₁ ∨
      x = (modifiedPrincipalCubicRootsReIm a b c d).x₂ := by
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  have key := cubic_roots_iff_of_real_depressed_root ha b c d (principalRealRoot p q)
    (principalRealRoot_spec p q) x
  simp only [principalRealRoot, radicandPlus, radicandMinus, discriminant_ofReal,
    realDiscriminant, p, q] at key
  rw [show ((modifiedPrincipalCubicRootsReIm a b c d).x₀ : ℂ) = _ from Complex.ofReal_sub _ _]
  exact key

end CubicEquation.CardanoReal
