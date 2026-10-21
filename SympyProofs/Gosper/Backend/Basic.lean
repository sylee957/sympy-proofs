module

public import SympyProofs.Gosper.Backend.Factorization
public import SympyProofs.Gosper.Backend.Rref

/-! CAS operations used by Gosper: factorization, resultant, matrix construction, and RREF.
Shift detection and linear solving are derived interpretations of these primitives.
The contracts do not assert correctness of any external Python implementation. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- The resultant eliminates the outer variable of `K[X][X]`, leaving a
polynomial in the inner variable. Its inputs are arbitrary bivariate polynomials;
the Gosper-specific translation is constructed by `Backend.shiftResultant`. -/
structure Backend (K : Type*) [Field K] where
  factor : K[X] → K × List (K[X] × ℕ)
  resultant : K[X][X] → K[X][X] → K[X]
  zeros : (m n : ℕ) → Matrix (Fin m) (Fin n) K
  setElement : {m n : ℕ} → Matrix (Fin m) (Fin n) K →
    Fin m → Fin n → K → Matrix (Fin m) (Fin n) K
  getCol : {m n : ℕ} → Matrix (Fin m) (Fin n) K → Fin n → Fin m → K
  rref : RrefOperation K

variable {K : Type*} [Field K]

/-- Factorization reconstructs the input into irreducible factors. Resultants
agree with the Sylvester determinant up to a nonzero coefficient (including sign).
RREF preserves the kernel and has the declared scaled pivot structure.
Matrix construction starts with zero entries and updates only the selected entry.
Column reads return the entries at the requested column.
Zero polynomial inputs are excluded from the polynomial contracts. -/
structure Backend.Valid (backend : Backend K) : Prop where
  factor_valid : ∀ p : K[X], p ≠ 0 → IsFactorization p (backend.factor p)
  resultant_eq : ∀ p q : K[X][X], p ≠ 0 → q ≠ 0 →
    ∃ c : K, c ≠ 0 ∧ backend.resultant p q = C c * Polynomial.resultant p q
  zeros_eq : ∀ m n, backend.zeros m n = 0
  setElement_apply : ∀ {m n} (M : Matrix (Fin m) (Fin n) K) i j value i' j',
    backend.setElement M i j value i' j' =
      if i' = i ∧ j' = j then value else M i' j'
  getCol_apply : ∀ {m n} (M : Matrix (Fin m) (Fin n) K) j i,
    backend.getCol M j i = M i j
  rref_valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (backend.rref A).Valid A

/-- Pair the reference polynomial primitives and functional matrix updates with a supplied RREF operation.
Linear solving is always interpreted from that RREF; it is not a backend field. -/
noncomputable def referenceBackend [DecidableEq K] (rref : RrefOperation K) : Backend K where
  factor := referenceFactor
  resultant p q := Polynomial.resultant p q
  zeros _ _ := 0
  setElement M i j value := Function.update M i (Function.update (M i) j value)
  getCol M j := fun i => M i j
  rref := rref

theorem referenceBackend_valid [DecidableEq K] (rref : RrefOperation K)
    (hrref : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A) :
    (referenceBackend rref).Valid where
  factor_valid := referenceFactor_valid
  resultant_eq p q _ _ := ⟨1, one_ne_zero, by simp [referenceBackend]⟩
  zeros_eq _ _ := rfl
  setElement_apply M i j value i' j' := by
    by_cases hi : i' = i <;> by_cases hj : j' = j <;>
      simp [referenceBackend, Function.update, hi, hj]
  getCol_apply _ _ _ := rfl
  rref_valid := hrref

/-- The natural roots used by Gosper are read from the backend's factor list. -/
noncomputable def Backend.nonnegativeIntegerRoots [DecidableEq K] [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (p : K[X]) : Finset ℕ :=
  nonnegativeIntegerRootsFromFactors (backend.factor p).2

theorem Backend.mem_nonnegativeIntegerRoots [DecidableEq K] [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)] (backend : Backend K)
    (h : backend.Valid) (p : K[X]) (hp : p ≠ 0) (n : ℕ) :
    n ∈ backend.nonnegativeIntegerRoots p ↔ p.eval (n : K) = 0 :=
  (h.factor_valid p hp).mem_nonnegativeIntegerRoots n

/-- A different sign convention for the resultant still satisfies its contract. -/
theorem Backend.Valid.scaleResultant {backend : Backend K} (h : backend.Valid)
    (c : K) (hc : c ≠ 0) :
    ({ backend with resultant := fun p q => C c * backend.resultant p q } : Backend K).Valid where
  factor_valid := h.factor_valid
  resultant_eq p q hp hq := by
    obtain ⟨d, hd, he⟩ := h.resultant_eq p q hp hq
    exact ⟨c * d, mul_ne_zero hc hd, by simp [he, map_mul, mul_assoc]⟩
  zeros_eq := h.zeros_eq
  setElement_apply := h.setElement_apply
  getCol_apply := h.getCol_apply
  rref_valid := h.rref_valid

end Gosper.Algorithm
