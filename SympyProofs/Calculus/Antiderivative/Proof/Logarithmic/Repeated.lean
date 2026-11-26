module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Poles
public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Denominator
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue

/-! Removing the repeated normal poles and the entire special pole from a common denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial Extension.SimplePole
open scoped Polynomial

variable {E F : Type} [Field E] [DecidableEq E] [Field F] [CharZero F]
local notation "ι" => algebraMap F[X] (RatFunc F)

/-- The formal derivative, weighted by the generator in an exponential extension. -/
def poleDerivative (exp : Bool) (T : Poly E) : Poly E :=
  if exp then Poly.X * T.derivative else T.derivative

/-- A saturated fraction satisfies every repeated- and special-pole divisibility row. -/
theorem repeated_dvd (j : E →+* F) (exp : Bool) (T : Poly E) (W : E[X]) (ht : T ≠ 0)
    (δ : Derivation ℤ F[X] F[X]) (D : Model.Der (RatFunc F))
    (compat : ∀ p, D (ι p) = ι (δ p)) (dx : exp = true → ∃ v, δ X = v * X)
    (h : Saturated D (ι (W.map j) / ι (Step.modelPoly j T))) :
    Poly.equiv (gcd T (poleDerivative exp T)) ∣ W := by
  let d := poleDerivative exp T
  let G := gcd T d
  let S := T / G
  let f := Step.modelPoly j
  have t0 : f T ≠ 0 := (Polynomial.map_ne_zero_iff j.injective).mpr
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr ht)
  have g0 : G ≠ 0 := by simp [G, gcd_eq_zero_iff, ht]
  have mul : f T = f G * f S := (congrArg f (EuclideanDomain.mul_div_cancel' g0
    (gcd_dvd_left T d)).symm).trans (map_mul ..)
  have bez : f (Step.bezout T d).1 * f T + f (Step.bezout T d).2 * f d = f G := by
    simpa only [map_add, map_mul, mul_comm (f T), mul_comm (f d)] using
      congrArg f (Step.bezout_spec T d)
  have hd : f G ∣ f d := map_dvd f (gcd_dvd_right ..)
  apply (Polynomial.map_dvd_map' j).mp
  change f G ∣ W.map j
  have hs := simple_of_saturated δ D compat h
  cases exp with
  | false =>
    have ed : f d = (f T).derivative := by simp [f, d, poleDerivative, derivative_map]
    rw [ed] at bez hd
    exact (simple_div_iff t0 mul bez hd _).mp hs
  | true =>
    have ed : f d = X * (f T).derivative := by simp [f, d, poleDerivative, derivative_map]
    rw [ed] at bez hd
    obtain ⟨v, hv⟩ := dx rfl
    exact (simple_integral_div_iff t0 mul bez hd _).mp ⟨hs, integral_of_saturated δ D compat hv h⟩

omit [CharZero F] in
/-- Canceling all detected common factors preserves the model rational function. -/
theorem cancel_repeated (j : E →+* F) (T d : Poly E) (W : E[X]) (ht : T ≠ 0)
    (h : Poly.equiv (gcd T d) ∣ W) :
    ι (W.map j) / ι (Step.modelPoly j T) =
      ι ((W / Poly.equiv (gcd T d)).map j) / ι (Step.modelPoly j (T / gcd T d)) := by
  let G := gcd T d
  have g0 : G ≠ 0 := by simp [G, gcd_eq_zero_iff, ht]
  have g1 := (map_ne_zero_iff _ Poly.equiv.injective).mpr g0
  have g2 := RatFunc.algebraMap_ne_zero ((Polynomial.map_ne_zero_iff j.injective).mpr g1)
  have nt := EuclideanDomain.mul_div_cancel' g0 (gcd_dvd_left T d)
  have nw := EuclideanDomain.mul_div_cancel' g1 h
  conv_lhs => rw [← nt, ← nw, map_mul, Polynomial.map_mul, map_mul, map_mul]
  exact mul_div_mul_left _ _ g2

end SympyProofs.Calculus.Antiderivative.Logarithmic
