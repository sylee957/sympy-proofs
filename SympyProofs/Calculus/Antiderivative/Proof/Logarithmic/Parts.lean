module

public import SympyProofs.Calculus.Antiderivative.Proof.LogRelations
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Clear

/-! Polynomial meaning of the rows and quotient arrays produced by the logarithmic step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial
open scoped Polynomial
open Step

variable {F : Type} [Field F] [DecidableEq F]

theorem combination_coeff (q : List ℚ) (ps : List (Poly F)) (i : ℕ) :
    (rationalPolynomial q ps).coeff i = rationalCombination q (ps.map (·.coeff i)) := by
  induction q generalizing ps with
  | nil => simp [rationalPolynomial, rationalCombination]
  | cons x q ih => cases ps <;> simp [rationalPolynomial, rationalCombination, ih]

private theorem combination_high (q : List ℚ) (ps : List (Poly F)) (i : ℕ)
    (hi : ∀ p ∈ ps, p.coeffs.length ≤ i) : (rationalPolynomial q ps).coeff i = 0 := by
  induction q generalizing ps with
  | nil => simp [rationalPolynomial]
  | cons x q ih =>
    cases ps with
    | nil => simp [rationalPolynomial]
    | cons p ps =>
      have h := hi _ List.mem_cons_self
      have hz : p.coeff i = 0 := by simp [Poly.coeff_eq_getD_coeffs, List.getD_eq_getElem?_getD, h]
      simp [rationalPolynomial, hz, ih ps (fun u hu => hi _ (List.mem_cons_of_mem _ hu))]

private theorem mem_drop_range {i n j : ℕ} : i ∈ (List.range n).drop j ↔ j ≤ i ∧ i < n := by
  rw [List.range_eq_range', List.drop_range', List.mem_range'_1]
  simp only [Nat.mul_one, Nat.zero_add]
  omega

/-- Each row at index i is exactly the i-th coefficient of the combined polynomial. -/
theorem slices_iff (q : List ℚ) (ps : List (Poly F)) (j : ℕ) :
    (∀ r ∈ (coefficientSlices ps).drop j, rationalCombination q r = 0) ↔
      ∀ i, j ≤ i → (rationalPolynomial q ps).coeff i = 0 := by
  let width := (ps.map fun p => p.coeffs.length).max?.getD 0
  simp only [coefficientSlices, ← List.map_drop, List.forall_mem_map, ← combination_coeff,
    mem_drop_range, and_imp]
  constructor
  · intro h i hi
    by_cases hw : i < width
    · exact h _ hi hw
    · apply combination_high
      exact fun p hp => (List.le_max?_getD_of_mem (List.mem_map_of_mem (f := fun p : Poly F =>
        p.coeffs.length) hp)).trans (Nat.le_of_not_lt hw)
  · exact fun h i hi _ => h i hi

theorem combination_mod (q : List ℚ) (ps : List (Poly F)) (s : Poly F) :
    rationalPolynomial q (ps.map (· % s)) = rationalPolynomial q ps % Poly.equiv s := by
  induction q generalizing ps with
  | nil => simp [rationalPolynomial]
  | cons x q ih =>
    cases ps with
    | nil => simp [rationalPolynomial]
    | cons p ps =>
      simp only [List.map_cons, rationalPolynomial, Poly.equiv_mod, ih, Polynomial.add_mod]
      rw [Step.scalar_mod]

theorem combination_div (q : List ℚ) (ps : List (Poly F)) (s : Poly F) :
    rationalPolynomial q (ps.map (· / s)) = rationalPolynomial q ps / Poly.equiv s := by
  induction q generalizing ps with
  | nil => simp [rationalPolynomial]
  | cons x q ih =>
    cases ps with
    | nil => simp [rationalPolynomial]
    | cons p ps =>
      simp only [List.map_cons, rationalPolynomial, Poly.equiv_div, ih, Polynomial.div_def,
        Polynomial.add_divByMonic, mul_add]
      rw [← Polynomial.smul_eq_C_mul (p := Poly.equiv p) (x : F),
        Polynomial.smul_divByMonic, Polynomial.smul_eq_C_mul]
      ring

/-- The zero nonconstant coefficient rows say exactly that the polynomial is constant. -/
theorem constant_slices (q : List ℚ) (ps : List (Poly F)) :
    (∀ r ∈ (coefficientSlices ps).drop 1, rationalCombination q r = 0) ↔
      rationalPolynomial q ps = C (rationalCombination q (ps.map (·.coeff 0))) := by
  rw [slices_iff, ← combination_coeff]
  constructor
  · intro h
    ext i
    cases i with
    | zero => simp
    | succ i => simp [h _ (Nat.le_add_left 1 i)]
  · intro h i hi
    rw [h, coeff_C_of_ne_zero (by omega)]

/-- For a fixed common denominator the displayed rows encode the repeated-pole divisibility
condition and the value of the remaining polynomial at infinity. -/
theorem poleRows_iff (q : List ℚ) (as : List (Poly F)) (g s : Poly F) :
    let ns := as.map (· / g)
    let ps := ns.map (· / s)
    (∀ r ∈ coefficientSlices (as.map (· % g)) ++ (coefficientSlices ps).drop 1,
      rationalCombination q r = 0) ↔
      Poly.equiv g ∣ rationalPolynomial q as ∧
        rationalPolynomial q ns / Poly.equiv s =
          C (rationalCombination q (ps.map (·.coeff 0))) := by
  dsimp only
  rw [List.forall_mem_append, constant_slices, combination_div]
  refine and_congr ?_ Iff.rfl
  have h := slices_iff q (as.map (· % g)) 0
  simp only [List.drop_zero, combination_mod, Nat.zero_le, forall_true_left] at h
  rw [h, ← EuclideanDomain.mod_eq_zero]
  constructor
  · intro hc
    ext i
    exact (hc i).trans (coeff_zero i).symm
  · intro hz i
    rw [hz, coeff_zero]

end SympyProofs.Calculus.Antiderivative.Logarithmic
