module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants
public import SympyProofs.Calculus.Antiderivative.Spec.Split

/-! Presenting a flat field as rational functions over its own height-zero constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- A coefficient-field isomorphism induces an isomorphism of rational function fields. -/
noncomputable def ratFuncEquiv {F G : Type} [Field F] [Field G] (e : F ≃+* G) :
    RatFunc F ≃+* RatFunc G :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv e)

private theorem ratFuncEquiv_C {F G : Type} [Field F] [Field G] (e : F ≃+* G) (a : F) :
    ratFuncEquiv e (RatFunc.C a) = RatFunc.C (e a) := by
  rw [← RatFunc.algebraMap_C, ratFuncEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    Polynomial.mapEquiv_apply, Polynomial.map_C, RatFunc.algebraMap_C]
  rfl

private theorem ratFuncEquiv_X {F G : Type} [Field F] [Field G] (e : F ≃+* G) :
    ratFuncEquiv e RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    Polynomial.mapEquiv_apply, Polynomial.map_X, RatFunc.algebraMap_X]

/-- All flat elements are rational functions of the parameters with coefficients in the
height-zero constant field, including when the original raw coefficient ring is not a field. -/
noncomputable def overConstants (n : ℕ) : K R n ≃+* M (K R 0) n :=
  match n with
  | 0 => (K.modelConstantsEquiv (R := K R 0) (K R 0)).symm
  | k + 1 =>
    (K.equiv.trans (Model.stepEquiv R k)).trans
      ((ratFuncEquiv (K.equiv.symm.trans (overConstants k))).trans
        (Model.stepEquiv (K R 0) k).symm)

@[simp] theorem overConstants_lift {n : ℕ} (x : K R n) :
    overConstants (n + 1) (K.lift x) = Model.includeVars (Nat.le_succ n) (overConstants n x) := by
  apply (Model.stepEquiv (K R 0) n).injective
  rw [Model.stepEquiv_include]
  simp only [overConstants, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
    K.stepEquiv_lift, ratFuncEquiv_C, RingEquiv.symm_apply_apply]

@[simp] theorem overConstants_gen {n : ℕ} :
    overConstants (R := R) (n + 1) K.gen =
      algebraMap (MvPolynomial (Fin (n + 1)) (K R 0)) _ (MvPolynomial.X (Fin.last n)) := by
  apply (Model.stepEquiv (K R 0) n).injective
  simp only [overConstants, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, K.stepEquiv_gen,
    ratFuncEquiv_X, Model.stepEquiv_last]

end SympyProofs.Calculus.Antiderivative.Factor
