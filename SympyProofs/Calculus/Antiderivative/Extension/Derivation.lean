module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Derivations of `F[θ]` and of the field of rational functions `F(θ)` over a field `F`.
A derivation of the polynomial ring extends to the field by the quotient rule (`extend`).
Over a differential field `F`, `affine a b` is the derivation of `F[θ]` that extends the one
of `F` with `θ′ = a θ + b`: adjoining a primitive `θ` of `b` takes `a = 0`, and adjoining an
exponential `θ` of `u` takes `a = u′` and `b = 0`. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension

open Polynomial

noncomputable local instance intAlgebraDerivation {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

private noncomputable def quotientRule {F : Type*} [Field F]
    (d : Derivation ℤ F[X] F[X]) (p q : F[X]) : RatFunc F :=
  let ι := algebraMap F[X] (RatFunc F)
  (ι (d p) * ι q - ι p * ι (d q)) / (ι q)^2

private noncomputable def fractionDeriv {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X])
    (f : RatFunc F) : RatFunc F :=
  f.liftOn' (quotientRule d) fun {p q a} hq ha => by
    simp only [quotientRule, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero ha]
    ring

private theorem fractionDeriv_div {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X]) (p q : F[X]) :
    fractionDeriv d (algebraMap _ _ p / algebraMap _ _ q) = quotientRule d p q := by
  unfold fractionDeriv
  apply RatFunc.liftOn'_div
  intro p
  simp [quotientRule]

private noncomputable def fractionAddHom {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X]) :
    RatFunc F →+ RatFunc F where
  toFun := fractionDeriv d
  map_zero' := by simpa [quotientRule] using fractionDeriv_div d (0 : F[X]) 1
  map_add' x y := by
    induction x using RatFunc.induction_on with
    | _ p q hq =>
      induction y using RatFunc.induction_on with
      | _ r s hs =>
        rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hq) (RatFunc.algebraMap_ne_zero hs)]
        simp only [← map_mul, ← map_add, fractionDeriv_div]
        simp only [quotientRule, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
        field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hs]
        ring

/-- Extend a derivation of the polynomial ring to the field of rational functions by the
quotient rule. -/
@[no_expose] noncomputable def extend {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X]) :
    Derivation ℤ (RatFunc F) (RatFunc F) where
  toFun := fractionDeriv d
  map_add' := (fractionAddHom d).map_add
  map_smul' n x := by
    simpa [fractionAddHom, Algebra.smul_def, zsmul_eq_mul] using (fractionAddHom d).map_zsmul n x
  map_one_eq_zero' := by
    change fractionDeriv d 1 = 0
    simpa [quotientRule] using fractionDeriv_div d (1 : F[X]) 1
  leibniz' x y := by
    change fractionDeriv d (x * y) = x * fractionDeriv d y + y * fractionDeriv d x
    induction x using RatFunc.induction_on with
    | _ p q hq =>
      induction y using RatFunc.induction_on with
      | _ r s hs =>
        rw [div_mul_div_comm]
        simp only [← map_mul, fractionDeriv_div]
        simp only [quotientRule, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
        field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hs]
        ring

theorem extend_div {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X]) (p q : F[X]) :
    let ι := algebraMap F[X] (RatFunc F)
    extend d (ι p / ι q) = (ι (d p) * ι q - ι p * ι (d q)) / (ι q)^2 :=
  fractionDeriv_div d p q

theorem extend_poly {F : Type*} [Field F] (d : Derivation ℤ F[X] F[X]) (p : F[X]) :
    extend d (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (d p) := by
  change fractionDeriv d _ = _
  simpa [quotientRule] using fractionDeriv_div d p 1

section

open Differential

variable {F : Type*} [Field F] [Differential F]

/-- The derivation of `F[θ]` that extends the one of `F` with `θ′ = a θ + b`. -/
noncomputable abbrev affine (a b : F) := implicitDeriv (C a * X + C b)

theorem coeff_affine (a b : F) (p : F[X]) (i : ℕ) :
    (affine a b p).coeff i =
      (p.coeff i)′ + (i : F) * a * p.coeff i + ((i + 1 : ℕ) : F) * b * p.coeff (i + 1) := by
  change (mapCoeffs p + (C a * X + C b) * p.derivative).coeff i = _
  cases i <;> simp [add_mul, mul_assoc, coeff_X_mul, coeff_derivative]
  ring

end

end SympyProofs.Calculus.Antiderivative.Extension
