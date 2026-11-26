module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Semantics
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Model

/-! Split a monomial at the last coordinate of its exponent vector. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

namespace Model

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Earlier variables give a constant polynomial in the last variable. -/
theorem splitPolynomial_rename (p : MvPolynomial (Fin n) R) :
    splitPolynomial R n (MvPolynomial.rename Fin.castSucc p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [splitPolynomial, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The lower exponents together with the last exponent recover the full monomial. -/
theorem split_exponents (e : Mono) :
    e.exponents (n + 1) =
      Finsupp.mapDomain Fin.castSucc (Mono.exponents n (e.take n)) +
        Finsupp.single (Fin.last n) (Poly.Raw.coeff e n) := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    have hn : Fin.last n ∉ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
      rintro ⟨j,h⟩
      exact Fin.castSucc_ne_last j h
    simp [Finsupp.mapDomain_of_notMem_range _ _ hn]
  | cast i =>
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n),
      Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i), add_zero]
    simp [Poly.Raw.coeff, List.getD_eq_getElem?_getD, i.isLt]

/-- A term of highest-variable degree `k` is the polynomial monomial of degree `k`
whose coefficient contains precisely the lower variables. -/
theorem splitPolynomial_monomial (e : Mono) (c : R) :
    splitPolynomial R n (MvPolynomial.monomial (e.exponents (n + 1)) c) =
      Polynomial.monomial (Poly.Raw.coeff e n)
        (MvPolynomial.monomial (Mono.exponents n (e.take n)) c) := by
  have he := split_exponents (n := n) e
  have h : MvPolynomial.monomial (e.exponents (n+1)) c =
      MvPolynomial.rename Fin.castSucc (MvPolynomial.monomial (Mono.exponents n (e.take n)) c) *
        MvPolynomial.X (Fin.last n) ^ Poly.Raw.coeff e n := by
    rw [MvPolynomial.rename_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, mul_one, ← he]
  rw [h, map_mul, map_pow, splitPolynomial_last, splitPolynomial_rename, C_mul_X_pow_eq_monomial]

end Model

end SympyProofs.Calculus.Antiderivative
