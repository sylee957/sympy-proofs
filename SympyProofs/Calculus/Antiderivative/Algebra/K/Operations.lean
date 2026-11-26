module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Defs
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Canonical
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Division
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The value of a raw fraction and the arithmetic identities needed to lift the operations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K.Raw

variable {R : Type} [CommRing R] (n : ℕ)

@[simp] theorem polyValue_nil : polyValue n ([] : MPoly.Raw R) = 0 := by simp [polyValue]

variable [DecidableEq R]

@[simp] theorem polyValue_C (r : R) : polyValue n (MPoly.Raw.C r) =
    algebraMap (MvPolynomial (Fin n) R) _ (MvPolynomial.C r) := by simp [polyValue]

@[simp] theorem polyValue_add (p q : MPoly.Raw R) :
    polyValue n (MPoly.Raw.add n p q) = polyValue n p + polyValue n q := by simp [polyValue]

@[simp] theorem polyValue_normalize (p : MPoly.Raw R) :
    polyValue n (MPoly.Raw.normalize n p) = polyValue n p := by simp [polyValue]

@[simp] theorem polyValue_mul (p q : MPoly.Raw R) :
    polyValue n (MPoly.Raw.mul n p q) = polyValue n p * polyValue n q := by simp [polyValue]

@[simp] theorem polyValue_neg (p : MPoly.Raw R) :
    polyValue n (MPoly.Raw.neg n p) = -polyValue n p := by simp [polyValue]

variable [IsDomain R]

omit [IsDomain R] in
/-- The equality test on lists decides equality of their polynomial values. -/
@[simp] theorem polyEq_iff (p q : MPoly.Raw R) :
    polyEq n p q = true ↔ polyValue n p = polyValue n q := by
  simp only [polyEq, Bool.or_eq_true, beq_iff_eq, MPoly.Raw.normalize_eq_iff_value, polyValue,
    (IsFractionRing.injective _ _).eq_iff, MPoly.Raw.toMvPolynomial, AddMonoidAlgebra.ofCoeff_inj]
  exact or_iff_right_of_imp (congrArg (MPoly.Raw.value n))

/-- Either zero part makes the field value zero. -/
@[simp] theorem isZero_iff (x : K.Raw R) : isZero n x = true ↔ value n x = 0 := by
  simp [isZero, value, div_eq_zero_iff]

/-- With nonzero denominators, cross multiplication decides field equality. -/
theorem beq_iff (x y : K.Raw R) : beq n x y = true ↔ value n x = value n y := by
  unfold beq
  split
  · rename_i hx
    rw [isZero_iff] at hx ⊢
    rw [hx, eq_comm]
  · rename_i hx
    split
    · rename_i hy
      rw [isZero_iff] at hx hy
      simp [hy, hx]
    · rename_i hy
      simp only [isZero_iff, value, div_eq_zero_iff, not_or] at hx hy
      rw [value, value, div_eq_div_iff hx.2 hy.2]
      split
      · rename_i hd
        rw [polyEq_iff] at hd ⊢
        rw [hd, mul_left_inj' hy.2]
      · simp

@[simp] theorem value_ofPoly (p : MPoly.Raw R) : value n (ofPoly p) = polyValue n p := by
  simp [value, ofPoly]

@[simp] theorem value_C (a : R) :
    value n (C a) = algebraMap (MvPolynomial (Fin n) R) _ (MvPolynomial.C a) := by simp [C]

@[simp] theorem value_neg (x : K.Raw R) : value n (neg n x) = -value n x := by
  simp [neg, value, neg_div]

omit [DecidableEq R] in
@[simp] theorem value_inv (x : K.Raw R) : value n (inv x) = (value n x)⁻¹ := by
  simp [inv, value]

variable [Div R] [NormalizedGCDMonoid R]

/-- Cancellation preserves the quotient even if the proposed divisor is inaccurate. -/
@[simp] theorem value_cancel (a b : MPoly.Raw R) :
    value n (cancel n a b) = polyValue n a / polyValue n b := by
  unfold cancel
  split
  · rfl
  · split
    · rename_i h
      simp only [Bool.or_eq_true, polyEq_iff, polyValue_nil] at h
      rcases h with ha | hb <;> simp [*]
    · rename_i h
      simp only [Bool.or_eq_true, polyEq_iff, polyValue_nil, not_or] at h
      have hb := h.2
      dsimp only
      split
      · rfl
      · split
        · rename_i a' b' ha' hb'
          have ha := congrArg (polyValue n) (MPoly.Raw.mul_of_divExact? ha')
          have hd := congrArg (polyValue n) (MPoly.Raw.mul_of_divExact? hb')
          simp only [polyValue_mul, polyValue_normalize] at ha hd
          have hg := right_ne_zero_of_mul (hd ▸ hb)
          rw [← ha, ← hd, mul_div_mul_right _ _ hg]
          rfl
        · rfl

omit [IsDomain R] in
/-- Multiplying each returned quotient by the removed factor recovers its input. -/
theorem factorPair_spec (a b : MPoly.Raw R) :
    let (u, v, g) := factorPair n a b
    polyValue n u * polyValue n g = polyValue n a ∧
      polyValue n v * polyValue n g = polyValue n b := by
  unfold factorPair
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · rename_i u v hu hv
        constructor
        · simpa only [polyValue_mul, polyValue_normalize] using
            congrArg (polyValue n) (MPoly.Raw.mul_of_divExact? hu)
        · simpa only [polyValue_mul, polyValue_normalize] using
            congrArg (polyValue n) (MPoly.Raw.mul_of_divExact? hv)
      · simp

@[simp] theorem value_add (x y : K.Raw R) :
    value n (add n x y) = value n x + value n y := by
  unfold add
  split
  · rename_i hx
    rw [(isZero_iff n x).mp hx, zero_add]
  · rename_i hx
    split
    · rename_i hy
      rw [(isZero_iff n y).mp hy, add_zero]
    · rename_i hy
      simp only [isZero_iff, value, div_eq_zero_iff, not_or] at hx hy
      split
      · rename_i hd
        rw [polyEq_iff] at hd
        rw [value_cancel, polyValue_add, value, value, hd, add_div]
      · have h₁ := factorPair_spec n x.den y.den
        generalize factorPair n x.den y.den = f at h₁ ⊢
        obtain ⟨b, d, g⟩ := f
        dsimp only at h₁ ⊢
        generalize ht : MPoly.Raw.add n (MPoly.Raw.mul n x.num d) (MPoly.Raw.mul n y.num b) = t
        have h₂ := factorPair_spec n t g
        generalize factorPair n t g = f at h₂ ⊢
        obtain ⟨u, v, w⟩ := f
        dsimp only at h₂ ⊢
        have ht' := congrArg (polyValue n) ht
        simp only [polyValue_add, polyValue_mul] at ht'
        have hb := left_ne_zero_of_mul (h₁.1 ▸ hx.2)
        have hg := right_ne_zero_of_mul (h₁.1 ▸ hx.2)
        have hd := left_ne_zero_of_mul (h₁.2 ▸ hy.2)
        have hv := left_ne_zero_of_mul (h₂.2 ▸ hg)
        simp only [value, polyValue_mul]
        rw [← h₁.1, ← h₁.2, ← h₂.2]
        have hw := right_ne_zero_of_mul (h₂.2 ▸ hg)
        field_simp
        linear_combination h₂.1.trans ht'.symm

@[simp] theorem value_mul (x y : K.Raw R) :
    value n (mul n x y) = value n x * value n y := by
  unfold mul
  dsimp only
  rw [value, polyValue_mul, polyValue_mul, ← div_mul_div_comm]
  change value n (cancel n x.num y.den) * value n (cancel n y.num x.den) = _
  rw [value_cancel, value_cancel]
  simp only [value, div_mul_div_comm, mul_comm (polyValue n y.den)]

end SympyProofs.Calculus.Antiderivative.K.Raw
