module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.ScalarRaw
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Operations

/-! Scalar fraction arithmetic agrees with the general field operations at every height. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K.Raw

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] (n : ℕ)

/-- The inclusion of coefficients into the model at a fixed height. -/
noncomputable def scalarHom : R →+* FractionRing (MvPolynomial (Fin n) R) :=
  (algebraMap (MvPolynomial (Fin n) R) _).comp MvPolynomial.C

omit [IsDomain R] [DecidableEq R] in
theorem scalarHom_injective : Function.Injective (scalarHom (R := R) n) :=
  (IsFractionRing.injective (MvPolynomial (Fin n) R) _).comp (MvPolynomial.C_injective _ _)

omit [IsDomain R] [DecidableEq R] in
theorem polyValue_of_scalar? (p : MPoly.Raw R) (a : R) (h : scalar? p = some a) :
    polyValue n p = scalarHom n a := by
  cases p with
  | nil => simp [scalar?] at h; simp [← h]
  | cons t p =>
    obtain ⟨e,c⟩ := t
    cases e <;> cases p <;> simp [scalar?] at h
    simp [h, polyValue, MPoly.Raw.toMvPolynomial_cons, Poly.Raw.trim, Mono.trim,
      MvPolynomial.monomial_zero', scalarHom]

omit [DecidableEq R] in
theorem value_of_scalars? (x : Raw R) {a b : R} (h : x.scalars? = some (a,b)) :
    value n x = scalarHom n a / scalarHom n b := by
  cases ha : scalar? x.num <;> cases hb : scalar? x.den <;> simp [scalars?, ha, hb] at h
  rcases h with ⟨rfl,rfl⟩
  rw [value, polyValue_of_scalar? n _ _ ha, polyValue_of_scalar? n _ _ hb]

variable [NormalizedGCDMonoid R] [Div R]

omit [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem value_scalarFraction (a b : R) :
    value n (scalarFraction a b) = scalarHom n a / scalarHom n b := by
  simp [scalarFraction, value, scalarHom]

@[simp] theorem value_reduceScalars (a b : R) :
    value n (reduceScalars a b) = scalarHom n a / scalarHom n b := by
  simp only [reduceScalars, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with hb hz hex hg hdiv
  · simp [hb, scalarHom]
  · rcases (by simpa using hz : a = 0 ∨ b = 0) with h | h <;> simp [h]
  · have hb0 : b ≠ 0 := fun h => hz (by simp [h])
    have hn := (map_ne_zero_iff _ (scalarHom_injective (R := R) n)).mpr hb0
    rw [value_C]
    apply (eq_div_iff hn).mpr
    exact (map_mul (scalarHom n) _ _).symm.trans (congrArg (scalarHom n) hex)
  · simp
  · let g := gcd a b
    have hga : a / g * g = a ∧ b / g * g = b := by simpa using hdiv
    have hgb : g ≠ 0 := fun h => hz (by
      have hb0 : b = 0 := hga.2.symm.trans (by rw [h, mul_zero])
      simp [hb0])
    have hgn := (map_ne_zero_iff _ (scalarHom_injective (R := R) n)).mpr hgb
    rw [value_scalarFraction]
    change scalarHom n (a / g) / scalarHom n (b / g) = _
    conv_rhs => rw [← hga.1, ← hga.2, map_mul, map_mul, mul_div_mul_right _ _ hgn]
  · simp

@[simp] theorem value_addScalars (x y : Raw R) :
    value n (addScalars n x y) = value n x + value n y := by
  unfold addScalars
  split
  · rename_i a b c d hx hy
    have h₁ := value_of_scalars? n x hx
    have h₂ := value_of_scalars? n y hy
    split_ifs with hb hd hbd
    · simp [h₁, hb]
    · simp [h₂, hd]
    · simp [h₁, h₂, hbd, add_div]
    · have hb' := (map_ne_zero_iff _ (scalarHom_injective (R := R) n)).mpr hb
      have hd' := (map_ne_zero_iff _ (scalarHom_injective (R := R) n)).mpr hd
      simp [h₁, h₂, div_add_div _ _ hb' hd', mul_comm (scalarHom n c)]
  · simp

@[simp] theorem value_mulScalars (x y : Raw R) :
    value n (mulScalars n x y) = value n x * value n y := by
  unfold mulScalars
  split
  · rename_i a b c d hx hy
    simp [value_of_scalars? n x hx, value_of_scalars? n y hy, div_mul_div_comm]
  · simp

end SympyProofs.Calculus.Antiderivative.K.Raw
