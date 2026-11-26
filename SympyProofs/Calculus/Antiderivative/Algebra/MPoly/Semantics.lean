module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Raw
public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-! The finitely supported coefficient function of a list of terms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Mono

/-- The exponents in the first `n` variables as a Mathlib monomial. -/
noncomputable def exponents (n : ℕ) (e : Mono) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => Poly.Raw.coeff e i

@[simp] theorem exponents_apply (n : ℕ) (e : Mono) (i : Fin n) :
    exponents n e i = Poly.Raw.coeff e i := rfl

@[simp] theorem exponents_trim (n : ℕ) (e : Mono) : exponents n e.trim = exponents n e := by
  ext i
  exact Poly.Raw.coeff_trim e i

@[simp] theorem exponents_nil (n : ℕ) : exponents n [] = 0 := by ext; rfl

/-- The list fits in the first `n` variables exactly when all later exponents vanish. -/
theorem fits_iff (n : ℕ) (e : Mono) :
    e.trim.length ≤ n ↔ ∀ j, n ≤ j → Poly.Raw.coeff e j = 0 := by
  constructor
  · intro h j hj
    rw [← Poly.Raw.coeff_trim]
    exact Poly.Raw.coeff_eq_zero_of_length_le (le_trans h hj)
  · intro h
    by_contra! hn
    have hz := h (Poly.Raw.natDegree e) (by change n ≤ e.trim.length - 1; omega)
    rw [Poly.Raw.coeff_natDegree] at hz
    exact Poly.Raw.leadingCoeff_ne_zero (by intro he; simp [he, trim] at hn) hz

theorem coeff_add (e d : Mono) (i : ℕ) :
    Poly.Raw.coeff (add e d) i = Poly.Raw.coeff e i + Poly.Raw.coeff d i := by
  induction e generalizing d i with
  | nil => simp [add, Poly.Raw.addAux]
  | cons a e ih =>
    cases d with
    | nil => simp [add, Poly.Raw.addAux]
    | cons b d =>
      cases i with
      | zero => rfl
      | succ i => exact ih d i

@[simp] theorem exponents_add (n : ℕ) (e d : Mono) :
    exponents n (add e d) = exponents n e + exponents n d := by ext i; exact coeff_add e d i

theorem fits_add (n : ℕ) (e d : Mono) :
    (add e d).trim.length ≤ n ↔ e.trim.length ≤ n ∧ d.trim.length ≤ n := by
  simp only [fits_iff, coeff_add, Nat.add_eq_zero_iff]
  grind

/-- Within the chosen variables the exponent vector determines the trimmed list. -/
theorem trim_eq_of_exponents_eq {n : ℕ} {e d : Mono} (he : e.trim.length ≤ n)
    (hd : d.trim.length ≤ n) (h : exponents n e = exponents n d) : e.trim = d.trim := by
  apply Poly.Raw.trim_congr
  intro j
  by_cases hj : j < n
  · exact DFunLike.congr_fun h ⟨j, hj⟩
  · rw [(fits_iff n e).mp he j (by omega), (fits_iff n d).mp hd j (by omega)]

end Mono

namespace MPoly.Raw

variable {R : Type*} [AddCommMonoid R]

/-- The coefficient function of one term, ignoring generators outside the given height. -/
noncomputable def term (n : ℕ) (e : Mono) (c : R) : (Fin n →₀ ℕ) →₀ R :=
  if e.trim.length ≤ n then Finsupp.single (e.exponents n) c else 0

/-- The coefficient function of a term list, adding the contributions of repeated monomials. -/
noncomputable def value (n : ℕ) : Raw R → ((Fin n →₀ ℕ) →₀ R)
  | [] => 0
  | (e, c) :: p => term n e c + value n p

@[simp] theorem term_zero (n : ℕ) (e : Mono) : term n e (0 : R) = 0 := by simp [term]

@[simp] theorem term_trim (n : ℕ) (e : Mono) (c : R) : term n e.trim c = term n e c := by
  simp [term, Mono.trim]

theorem term_add (n : ℕ) (e : Mono) (a b : R) :
    term n e (a + b) = term n e a + term n e b := by
  by_cases h : e.trim.length ≤ n <;> simp [term, h, Finsupp.single_add]

theorem value_append (n : ℕ) (p q : Raw R) :
    value n (p ++ q) = value n p + value n q := by
  induction p with
  | nil => simp [value]
  | cons a p ih => rcases a with ⟨e,c⟩; simp [value, ih, add_assoc]

variable [DecidableEq R]

theorem value_merge (n : ℕ) (p q : Raw R) :
    value n (merge p q) = value n p + value n q := by
  fun_induction merge p q with
  | case1 | case2 => simp [value]
  | case3 a ps d b qs tail hz ih =>
    change value n (merge ps qs) = _
    rw [ih]
    simp only [value,add_add_add_comm (term n d a) (value n ps) (term n d b),← term_add,hz,
      term_zero,zero_add]
  | case4 a ps d b qs tail hz ih =>
    change term n d (a+b) + value n (merge ps qs) = _
    rw [ih, term_add]
    simp only [value]
    ac_rfl
  | case5 => simp_all [value,add_assoc]
  | case6 => simp_all [value,add_assoc,add_left_comm]

theorem value_insert (n : ℕ) (e : Mono) (c : R) (p : Raw R) :
    value n (insert e c p) = term n e c + value n p := by
  induction p with
  | nil => by_cases hc : c = 0 <;> simp [insert, hc, value]
  | cons a p ih =>
    rcases a with ⟨d,b⟩
    by_cases hc : c = 0
    · simp [insert, hc, value]
    by_cases h : e = d
    · subst d
      by_cases hb : c + b = 0
      · simp [insert, hc, hb, value, ← add_assoc, ← term_add]
      · simp [insert, hc, hb, value, term_add, add_assoc]
    · by_cases ho : e.before d <;> simp [insert, hc, h, ho, value, ih, add_left_comm]

/-- Sorting and merging terms preserves the coefficient function. -/
@[simp] theorem value_normalize (n : ℕ) (p : Raw R) : value n (normalize n p) = value n p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    by_cases h : e.trim.length ≤ n
    · simp [normalize, h, value_insert, ih, value]
    · simp [normalize, h, ih, value, term]

end MPoly.Raw

namespace MPoly.Raw

variable {R : Type*} [CommRing R]

/-- Mathlib's polynomial with the coefficients of the term list. -/
noncomputable def toMvPolynomial (n : ℕ) (p : Raw R) : MvPolynomial (Fin n) R :=
  AddMonoidAlgebra.ofCoeff (value n p)

@[simp] theorem toMvPolynomial_nil (n : ℕ) : toMvPolynomial n ([] : Raw R) = 0 := rfl

theorem toMvPolynomial_cons (n : ℕ) (e : Mono) (c : R) (p : Raw R) :
    toMvPolynomial n ((e,c) :: p) =
      (if e.trim.length ≤ n then MvPolynomial.monomial (Mono.exponents n e) c else 0) +
        toMvPolynomial n p := by
  by_cases h : e.trim.length ≤ n <;>
    simp [toMvPolynomial, value, term, h, ← MvPolynomial.single_eq_monomial]

theorem toMvPolynomial_append (n : ℕ) (p q : Raw R) :
    toMvPolynomial n (p ++ q) = toMvPolynomial n p + toMvPolynomial n q := by
  simp [toMvPolynomial, value_append]

variable [DecidableEq R]

@[simp] theorem toMvPolynomial_normalize (n : ℕ) (p : Raw R) :
    toMvPolynomial n (normalize n p) = toMvPolynomial n p := by simp [toMvPolynomial]

@[simp] theorem toMvPolynomial_add (n : ℕ) (p q : Raw R) :
    toMvPolynomial n (add n p q) = toMvPolynomial n p + toMvPolynomial n q := by
  simp [add, toMvPolynomial, value_merge, AddMonoidAlgebra.ofCoeff_add]

@[simp] theorem toMvPolynomial_neg (n : ℕ) (p : Raw R) :
    toMvPolynomial n (neg n p) = -toMvPolynomial n p := by
  unfold neg
  rw [toMvPolynomial_normalize]
  induction p with
  | nil => simp
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    by_cases h : e.trim.length ≤ n <;> simp [toMvPolynomial_cons, h, ih, neg_add_rev, add_comm]

omit [DecidableEq R] in
private theorem toMvPolynomial_mulTerm (n : ℕ) (e : Mono) (a : R) (q : Raw R) :
    toMvPolynomial n (q.map fun (d,b) => (Mono.add e d, a * b)) =
      (if e.trim.length ≤ n then MvPolynomial.monomial (e.exponents n) a else 0) *
        toMvPolynomial n q := by
  induction q with
  | nil => simp
  | cons v q ih =>
    rcases v with ⟨d,b⟩
    by_cases he : e.trim.length ≤ n <;> by_cases hd : d.trim.length ≤ n <;>
      simp [toMvPolynomial_cons, Mono.fits_add, he, hd, ih, mul_add,
        MvPolynomial.monomial_mul_monomial]

@[simp] theorem toMvPolynomial_mul (n : ℕ) (p q : Raw R) :
    toMvPolynomial n (mul n p q) = toMvPolynomial n p * toMvPolynomial n q := by
  unfold mul
  rw [toMvPolynomial_normalize]
  induction p with
  | nil => simp [productRows]
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    have hm (a b : Raw R) :
        toMvPolynomial n (merge a b) = toMvPolynomial n a + toMvPolynomial n b := by
      simp [toMvPolynomial,value_merge]
    rw [productRows,hm,toMvPolynomial_mulTerm,toMvPolynomial_cons,ih,add_mul]

@[simp] theorem toMvPolynomial_C (n : ℕ) (c : R) :
    toMvPolynomial n (C c) = MvPolynomial.C c := by
  by_cases hc : c = 0
  · simp [C, hc]
  · simp [C, hc, toMvPolynomial_cons, Mono.trim, Poly.Raw.trim, MvPolynomial.monomial_zero']

end MPoly.Raw

end SympyProofs.Calculus.Antiderivative
