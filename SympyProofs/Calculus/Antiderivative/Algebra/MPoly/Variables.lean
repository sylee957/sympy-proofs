module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Variables and partial derivatives in the sparse polynomial model. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Mono

private theorem coeff_lower (e : Mono) (i j : ℕ) :
    Poly.Raw.coeff (e.modify i (· - 1)) j =
      if i = j then Poly.Raw.coeff e j - 1 else Poly.Raw.coeff e j := by
  by_cases h : i = j
  · subst j
    simp only [Poly.Raw.coeff, List.getD_eq_getElem?_getD, List.getElem?_modify_eq, ite_true]
    cases e[i]? <;> rfl
  · simp [Poly.Raw.coeff, List.getD_eq_getElem?_getD, List.getElem?_modify_ne _ _ h, h]

/-- Lowering the exponent of a variable in range preserves the bound on the variables. -/
theorem fits_lower {n : ℕ} (e : Mono) (i : Fin n) :
    (trim (e.modify i (· - 1))).length ≤ n ↔ e.trim.length ≤ n := by
  simp only [fits_iff, coeff_lower]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [ite_eq_right (by omega)]

/-- Decrementing an exponent subtracts a singleton from the exponent vector. -/
theorem exponents_lower {n : ℕ} (e : Mono) (i : Fin n) :
    exponents n (e.modify i (· - 1)) = exponents n e - Finsupp.single i 1 := by
  ext j
  by_cases h : i = j
  · subst j
    simp [Finsupp.tsub_apply, coeff_lower]
  · simp [Finsupp.tsub_apply, coeff_lower, Fin.val_ne_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]

private theorem coeff_power_one (i j : ℕ) :
    Poly.Raw.coeff (power i 1) j = if i = j then 1 else 0 := by
  induction i generalizing j with
  | zero => cases j <;> simp [power, Poly.Raw.coeff]
  | succ i ih =>
    cases j with
    | zero => simp [power, Poly.Raw.coeff, List.replicate_succ]
    | succ j => simpa [power, Poly.Raw.coeff, List.replicate_succ] using ih j

/-- The exponent vector of a variable is one at its index and zero elsewhere. -/
theorem exponents_var {n : ℕ} (i : Fin n) :
    exponents n (power i 1) = Finsupp.single i 1 := by
  ext j
  by_cases h : i = j
  · subst j
    simp [coeff_power_one]
  · simp [coeff_power_one, Fin.val_ne_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]

/-- A variable whose index lies below the tower height fits at that height. -/
theorem fits_var {n : ℕ} (i : Fin n) : (power i 1).trim.length ≤ n := by
  rw [fits_iff]
  intro j hj
  rw [coeff_power_one, ite_eq_right (by omega)]

end Mono

namespace MPoly.Raw

variable {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}

/-- A valid generator represents the corresponding Mathlib variable. -/
@[simp] theorem toMvPolynomial_X (i : Fin n) :
    toMvPolynomial n (X n i : Raw R) = MvPolynomial.X i := by
  nontriviality R
  simp [X, i.isLt, toMvPolynomial_cons, Mono.fits_var, Mono.exponents_var, MvPolynomial.X]

/-- The partial derivative on lists acts as the usual partial derivative on polynomials. -/
@[simp] theorem toMvPolynomial_partial (i : Fin n) (p : Raw R) :
    toMvPolynomial n (MPoly.Raw.partial n i p) = MvPolynomial.pderiv i (toMvPolynomial n p) := by
  simp only [MPoly.Raw.partial, i.isLt, ite_true, toMvPolynomial_normalize]
  induction p with
  | nil => simp
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    simp only [List.map_cons, toMvPolynomial_cons, ih]
    by_cases h : e.trim.length ≤ n <;>
      simp [Mono.fits_lower, h, Mono.exponents_lower,
        Poly.Raw.coeff, mul_comm]

end MPoly.Raw

namespace MPoly

variable {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}

/-- The polynomial variable corresponds to the same variable in the model. -/
@[simp] theorem equiv_X (i : Fin n) : equiv (X i : MPoly n R) = MvPolynomial.X i :=
  Raw.toMvPolynomial_X i

/-- The partial derivative with respect to variable number `i`. -/
def pderiv (i : ℕ) (p : MPoly n R) : MPoly n R := ofRaw (Raw.partial n i p.terms)

/-- Partial differentiation agrees with Mathlib's derivation in each generator. -/
@[simp] theorem equiv_pderiv (i : Fin n) (p : MPoly n R) :
    equiv (pderiv i p) = MvPolynomial.pderiv i (equiv p) := by
  induction p using induction_on with
  | h p => simp [pderiv]

/-- Partial differentiation is additive. -/
@[simp] theorem pderiv_add (i : Fin n) (a b : MPoly n R) :
    pderiv i (a + b) = pderiv i a + pderiv i b := equiv.injective (by simp)

/-- The product rule for sparse polynomials. -/
theorem pderiv_mul (i : Fin n) (a b : MPoly n R) :
    pderiv i (a * b) = pderiv i a * b + a * pderiv i b :=
  equiv.injective (by simp [mul_comm, add_comm])

/-- Coefficients have zero partial derivatives. -/
@[simp] theorem pderiv_C (i : Fin n) (a : R) : pderiv i (C a : MPoly n R) = 0 :=
  equiv.injective (by simp)

/-- The partial derivative of a variable is its Kronecker delta. -/
@[simp] theorem pderiv_X (i j : Fin n) :
    pderiv i (X j : MPoly n R) = if i = j then 1 else 0 := by
  apply equiv.injective
  by_cases h : i = j <;> simp [h, MvPolynomial.pderiv_X]

end MPoly

end SympyProofs.Calculus.Antiderivative
