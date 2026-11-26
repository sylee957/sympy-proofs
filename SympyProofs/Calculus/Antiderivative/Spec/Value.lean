module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Heights
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Derivation

/-! Interpretation in a model whose field of coefficients contains the original coefficient ring. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] (k : Type) [Field k]
variable [Algebra R k] [FaithfulSMul R k] {n m : ℕ}

namespace Model

/-- Extend the coefficients of a rational function along the given ring embedding. -/
noncomputable def mapCoefficients : M R n →+* M k n :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial (Fin n) k) _).comp
    (MvPolynomial.map (algebraMap R k)))
    ((IsFractionRing.injective _ _).comp
      (MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R k)))

@[simp] theorem mapCoefficients_polynomial (p : MvPolynomial (Fin n) R) :
    mapCoefficients k (algebraMap _ (M R n) p) =
      algebraMap _ _ (MvPolynomial.map (algebraMap R k) p) :=
  IsFractionRing.lift_algebraMap _ _

/-- Extending the coefficients commutes with adjoining any number of new variables. -/
theorem mapCoefficients_includeVars (h : n ≤ m) (x : M R n) :
    mapCoefficients k (includeVars h x) = includeVars h (mapCoefficients k x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) R) x
  simp [map_div₀, MvPolynomial.map_rename]

/-- Differentiate a model fraction in variable `i` by the quotient rule. -/
noncomputable def pderiv (i : ℕ) (x : M k n) : M k n :=
  if hi : i < n then
    let ab := IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) k)) x
    K.quotientRule (algebraMap _ _) (MvPolynomial.pderiv (⟨i, hi⟩ : Fin n)) ab.1 ab.2
  else 0

/-- Every polynomial presentation of a fraction gives the same partial derivative. -/
theorem pderiv_div (i : Fin n) (a b : MvPolynomial (Fin n) k) :
    pderiv k i (algebraMap _ (M k n) a / algebraMap _ (M k n) b) =
      K.quotientRule (algebraMap _ _) (MvPolynomial.pderiv i) a b := by
  rw [pderiv, dite_eq_left i.isLt]
  apply K.quotientRule_congr _ _ (IsFractionRing.injective _ _)
  rw [← IsFractionRing.mk'_eq_div, IsLocalization.mk'_sec]

/-- Sum generator velocities times the corresponding partial derivatives in the model. -/
noncomputable def weightedPartials (x : M k n) (i : ℕ) : List (M k n) → M k n
  | [] => 0
  | v :: vs => v * pderiv k i x + weightedPartials x (i + 1) vs

/-- The model derivative for a list of generator velocities in increasing index order. -/
noncomputable def der (v : List (M k n)) (x : M k n) : M k n :=
  weightedPartials k x 0 (v.take n)

end Model

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- The interpretation of a computable field element in a model with a larger constant field. -/
noncomputable def val : K R n →+* M k n :=
  (Model.mapCoefficients k).comp K.equiv.toRingHom

/-- Model values distinguish all elements of the computable field. -/
theorem val_injective : Function.Injective (val (R := R) (n := n) k) :=
  (val (R := R) (n := n) k).injective

@[simp] theorem val_ofPoly (p : MPoly n R) : val k (K.ofPoly p) =
    algebraMap _ _ (MvPolynomial.map (algebraMap R k) (MPoly.equiv p)) := by simp [val]

@[simp] theorem val_gen : val k (K.gen : K R (n + 1)) =
    algebraMap (MvPolynomial (Fin (n + 1)) k) _ (MvPolynomial.X (Fin.last n)) := by
  simp [val]

@[simp] theorem val_includeVars (h : n ≤ m) (x : K R n) :
    val k (K.includeVars h x) = Model.includeVars h (val k x) := by
  change Model.mapCoefficients k (K.equiv (K.includeAt h x)) = _
  have hx : K.equiv (K.includeAt h x) = Model.includeVars h (K.equiv x) :=
    Quotient.inductionOn x (K.Raw.value_atHeight h)
  exact (congrArg (Model.mapCoefficients k) hx).trans (Model.mapCoefficients_includeVars k h _)

@[simp] theorem val_lift (x : K R n) :
    val k (K.lift x) = Model.includeVars (Nat.le_succ n) (val k x) := val_includeVars k _ _

@[simp] theorem val_ofConst (x : K R 0) :
    val k (K.ofConst x : K R n) = Model.includeVars (Nat.zero_le n) (val k x) :=
  val_includeVars k _ _

/-- Partial differentiation commutes with interpretation in the model. -/
theorem val_pderiv (i : ℕ) (x : K R n) :
    val k (K.pderiv i x) = Model.pderiv k i (val k x) := by
  by_cases h : i < n
  · let j : Fin n := ⟨i, h⟩
    obtain ⟨a, b, _, hx⟩ := IsFractionRing.div_surjective (MPoly n R) x
    change K.ofPoly a / K.ofPoly b = x at hx
    rw [← hx, K.pderiv_div_ofPoly j]
    simp only [map_div₀, map_sub, map_mul, map_pow, val_ofPoly, MPoly.equiv_pderiv]
    rw [Model.pderiv_div k j, K.quotientRule, MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]
  · rw [K.pderiv_outside i (Nat.le_of_not_lt h), map_zero, Model.pderiv, dite_eq_right h]

/-- The model derivative of a value equals the value of its computed derivative. -/
theorem val_der (v : List (K R n)) (x : K R n) :
    val k (K.der v x) = Model.der k (v.map (val k)) (val k x) := by
  rw [K.der_eq_weightedPartials, Model.der, ← List.map_take]
  generalize v.take n = w
  suffices h : ∀ i, val k (K.weightedPartials x i w) =
      Model.weightedPartials k (val k x) i (w.map (val k)) from h 0
  induction w with
  | nil => simp [K.weightedPartials, Model.weightedPartials]
  | cons a w ih =>
    intro i
    simp [K.weightedPartials_cons, Model.weightedPartials, val_pderiv, ih]

end SympyProofs.Calculus.Antiderivative
