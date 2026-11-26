module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Parts
public import SympyProofs.Calculus.Antiderivative.Spec.Split

/-! The model fraction represented by the common denominator and rationally combined numerators. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial
open scoped Polynomial
open Step

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

private theorem rationalCombination_cons {F : Type} [Field F] (c : ℚ) (cs : List ℚ)
    (a : F) (as : List F) : rationalCombination (c :: cs) (a :: as) =
      (c : F) * a + rationalCombination cs as := rfl

private theorem common_value {as : List (Poly (K R n))} {ws : List (K R (n+1))}
    (d : RatFunc (M k n)) (q : List ℚ)
    (h : List.Forall₂ (fun x P => ι ((Poly.equiv P).map (val k)) =
      Model.stepEquiv k n (val k x) * d) ws as) :
    ι ((rationalPolynomial q as).map (val k)) =
      Model.stepEquiv k n (val k (rationalCombination q ws)) * d := by
  induction h generalizing q with
  | nil => cases q <;> simp [rationalPolynomial, rationalCombination]
  | cons hx ht ih =>
    cases q with
    | nil => simp [rationalPolynomial, rationalCombination]
    | cons c cs =>
      simp only [rationalPolynomial, rationalCombination_cons, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, map_add, map_mul, RatFunc.algebraMap_C,
        map_ratCast, hx, ih]
      ring

/-- Reading the newest generators of a rational combination gives exactly the quotient of
the interpreted combined numerator by the interpreted common denominator. -/
theorem value_commonDen (ws : List (K R (n+1))) (q : List ℚ) :
    let data := commonDen ws
    data.2 ≠ 0 ∧ data.1.length = ws.length ∧
      Model.stepEquiv k n (val k (rationalCombination q ws)) =
        ι ((rationalPolynomial q data.1).map (val k)) / ι ((Poly.equiv data.2).map (val k)) := by
  obtain ⟨d0, hf⟩ := commonDen_numerators ws
  have h0 : (commonDen ws).2 ≠ 0 := fun h => d0 (by rw [h, ← K.joinPolyHom_apply, map_zero])
  have hn := (map_ne_zero_iff (Model.stepEquiv k n) (Model.stepEquiv k n).injective).mpr
    ((map_ne_zero_iff (val k) (val_injective k)).mpr d0)
  rw [val_joinPoly] at hn
  refine ⟨h0, hf.length_eq.symm, (eq_div_iff hn).mpr ?_⟩
  apply Eq.symm
  apply common_value
  refine hf.imp fun x P he => ?_
  rw [← val_joinPoly, he, map_mul, map_mul, val_joinPoly]

/-- Appending one coefficient and one additional generator appends its rational contribution. -/
theorem combination_append {F : Type} [Field F] (q : List ℚ) (xs : List F) (e : ℚ) (x : F)
    (h : q.length = xs.length) : rationalCombination (q ++ [e]) (xs ++ [x]) =
      rationalCombination q xs + (e : F) * x := by
  induction q generalizing xs with
  | nil =>
    obtain rfl := List.length_eq_zero_iff.mp h.symm
    simp [rationalCombination]
  | cons c q ih =>
    cases xs with
    | nil => simp at h
    | cons a xs =>
      simp only [List.cons_append, rationalCombination_cons, ih _ (Nat.succ.inj h), add_assoc]

end SympyProofs.Calculus.Antiderivative.Logarithmic
