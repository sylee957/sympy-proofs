module

public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Exp
public import SympyProofs.Calculus.Antiderivative.Proof.Liouville
public import SympyProofs.Calculus.Antiderivative.Proof.Answer
public import SympyProofs.Calculus.Antiderivative.Spec.Split

/-! A complete integration decision for the Laurent-polynomial part of an exponential step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Exp

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable {t : Tower R n} {lower : Level R n}

private theorem val_laurent (p : Poly (K R n)) (s : ℕ) :
    Model.stepEquiv k n (val k (K.joinPoly p / K.gen ^ s)) =
      algebraMap _ _ ((Poly.equiv p).map (val k)) / RatFunc.X ^ s := by
  simp [val_joinPoly]

private theorem laurent_identity (hs : lower.SolveSpec k t) (u : K R n) (s : ℕ)
    (p : Poly (K R n)) {cs : List (K R n)}
    (hc : coefficients lower (t.D u) s 0 p.coeffs = some cs) :
    Model.includeVars (Nat.le_succ n) (val k (p.coeff s)) +
      (t.step (.exp u)).modelD k (val k (K.joinPoly (Poly.ofList cs) / K.gen ^ s)) =
        val k (K.joinPoly p / K.gen ^ s) := by
  let du := val k (t.D u)
  let P := (Poly.equiv p).map (val k)
  let Q := (Poly.equiv (Poly.ofList cs)).map (val k)
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k (.exp u))⟩
  let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) :=
    ⟨fun a => Model.extendVariable_C _ _ a⟩
  have dx : Differential.deriv (RatFunc.X : RatFunc (M k n)) = RatFunc.C du * RatFunc.X := by
    change Model.extendVariable _ _ _ = _
    simp [Tower.modelVelocity, du]
  let A := Extension.affine du 0 Q - C ((s : M k n) * du) * Q
  have hp : P = C (val k (p.coeff s)) * X^s + A := by
    ext i
    have h := (coefficients_sound k hs hc).2 i
    simp only [Nat.zero_add] at h
    simp only [P, Q, A, coeff_add, coeff_X_pow, coeff_sub, Extension.coeff_affine,
      coeff_C_mul, coeff_map, Poly.coeff_equiv, Poly.coeff_ofList, mul_zero, zero_mul, add_zero]
    by_cases hi : i = s
    · subst i
      simp only [ite_true] at h ⊢
      rw [h, map_zero]
      simp
    · rw [ite_eq_right hi] at h ⊢
      rw [mul_zero]
      rw [Poly.coeff_eq_getD_coeffs]
      change t.modelD k _ + _ * du * _ = _ at h
      change _ = 0 + (t.modelD k _ + _ * du * _ - _ * du * _)
      linear_combination -h
  apply (Model.stepEquiv k n).injective
  rw [map_add, Model.stepEquiv_includeVars, Tower.stepEquiv_modelD, val_laurent, val_laurent]
  change _ + Differential.deriv (algebraMap _ _ Q / RatFunc.X ^ s) =
    algebraMap (Polynomial (M k n)) (RatFunc (M k n)) P / RatFunc.X ^ s
  rw [Extension.LiouvilleForm.deriv_div_X_pow dx, hp, map_add, add_div]
  congr 1
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, mul_div_assoc,
    div_self (pow_ne_zero s RatFunc.X_ne_zero), mul_one]

/-- Positive and negative decisions for a Laurent polynomial are correct for every admissible
lower model, including after extending the constants. -/
theorem integrate_spec [CharZero k] (hs : lower.SolveSpec k t) (hi : lower.IntegrateSpec k t)
    (ht : t.Admissible k) (u : K R n) (p : Poly (K R n)) (s : ℕ) :
    match integrate t.D u lower p s with
    | .elementary a => a.Regular k ∧
      a.deriv k (t.step (.exp u)) = val k (K.joinPoly p / K.gen ^ s)
    | .nonelementary => ¬ (t.step (.exp u)).Elementary k (val k (K.joinPoly p / K.gen ^ s)) := by
  let P := (Poly.equiv p).map (val k)
  have hn (h : (t.step (.exp u)).Elementary k (val k (K.joinPoly p / K.gen ^ s))) :
      t.Elementary k (P.coeff s) ∧ ∀ j : ℕ, j ≠ s → ∃ y : M k n,
        t.modelD k y + ((j : M k n) - s) * val k (t.D u) * y = P.coeff j := by
    apply t.elementary_exp_laurent_necessary k u ht
    rwa [← val_laurent, RingEquiv.symm_apply_apply]
  cases hc : coefficients lower (t.D u) s 0 p.coeffs with
  | none =>
    simp only [integrate, hc]
    intro he
    obtain ⟨cs,hcs⟩ := coefficients_complete k hs (t.D u) s 0 p.coeffs fun i _ his => by
      simpa [P, Poly.coeff_eq_getD_coeffs] using (hn he).2 i (by simpa using his)
    simp [hc] at hcs
  | some cs =>
    have h := hi (p.coeff s)
    cases hl : lower.integrate (p.coeff s) with
    | nonelementary =>
      simp only [integrate, hc, hl]
      rw [hl] at h
      exact fun he => h (by simpa [P] using (hn he).1)
    | elementary a =>
      simp only [integrate, hc, hl, Answer.regular_addField, Answer.regular_lift,
        Answer.deriv_addField, Answer.deriv_lift]
      rw [hl] at h
      exact ⟨h.1, h.2 ▸ laurent_identity k hs u s p hc⟩

end SympyProofs.Calculus.Antiderivative.Kind.Exp
