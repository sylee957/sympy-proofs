module

public import SympyProofs.Gosper.Applications

/-! # Cubic applications: equations (13), (14), and (16) -/

@[expose] public section
noncomputable section

namespace Gosper

variable {K : Type*} [Field K]

/-- The augmented coefficient matrix printed in (13). -/
def cubicMatrix (a b c d e : K) : Matrix (Fin 5) (Fin 5) K :=
  !![-d, -d, -d, e - d + c + b + a, 1;
     -3 * d - c, -2 * d - c, e - d + b + a, 2 * b + 3 * a, 0;
     -3 * d - 3 * c - b, e - d - c + a, b + 3 * a, 3 * a, 0;
     e - d - 2 * c - 2 * b, 2 * a, 2 * a, 0, 0;
     -b, a, 0, 0, 0]

/-- The determinant factorization (14). -/
theorem cubicMatrix_det (a b c d e : K) :
    (cubicMatrix a b c d e).det =
      a * (e - d) * (3 * a * e - 3 * a * d - 6 * a * c + 2 * b ^ 2 - 6 * a ^ 2) := by
  calc
    (cubicMatrix a b c d e).det =
        (!![-3*d-c, -2*d-c, e-d+b+a, 2*b+3*a;
          -3*d-3*c-b, e-d-c+a, b+3*a, 3*a;
          e-d-2*c-2*b, 2*a, 2*a, 0; -b, a, 0, 0] : Matrix (Fin 4) (Fin 4) K).det := by
      rw [Matrix.det_succ_column _ (4 : Fin 5)]
      norm_num [cubicMatrix, Fin.sum_univ_succ]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    _ = b * (!![-2*d-c, e-d+b+a, 2*b+3*a; e-d-c+a, b+3*a, 3*a;
          2*a, 2*a, 0] : Matrix (Fin 3) (Fin 3) K).det +
        a * (!![-3*d-c, e-d+b+a, 2*b+3*a; -3*d-3*c-b, b+3*a, 3*a;
          e-d-2*c-2*b, 2*a, 0] : Matrix (Fin 3) (Fin 3) K).det := by
      rw [Matrix.det_succ_row _ (3 : Fin 4)]
      norm_num [Fin.sum_univ_succ]
      congr 2
    _ = _ := by simp [Matrix.det_fin_three]; ring

def quarticNumerator (b c x : K) : K :=
  6 * x ^ 4 + (6 * b + 30) * x ^ 3 + (12 * b + 12 * c + 78) * x ^ 2 +
    ((2 * b + 42) * c - 4 * b ^ 2 - 10 * b + 138) * x +
      6 * c ^ 2 - (b ^ 2 + 14 * b - 75) * c + 2 * b ^ 3 - 74 * b + 168

/-- Consistency of the coefficient system (13) forces (14). -/
theorem cubic_system_necessary (a b c d e : K) (u : Fin 4 → K)
    (h : ∀ i : Fin 5, (∑ j : Fin 4, cubicMatrix a b c d e i j.castSucc * u j) =
      if i = 0 then 1 else 0) :
    a * (e - d) * (3 * a * e - 3 * a * d - 6 * a * c + 2 * b ^ 2 - 6 * a ^ 2) = 0 := by
  rw [← cubicMatrix_det]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (v := Fin.snoc u (-1)) (i := 4)
  · funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, h]
    fin_cases i <;> simp [cubicMatrix]
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    change (Fin.snoc u (-1) : Fin 5 → K) (Fin.last 4) ≠ 0
    rw [Fin.snoc_last]
    exact neg_ne_zero.mpr one_ne_zero

/-- The parameter substitution on p. 42 gives the asserted shifted common
root `n = -α`. It is the input to the cancellation step (6'). -/
theorem cubic_shifted_common_root (b c α : K) (j : ℕ) :
    cubic 1 b c ((α + 1) * ((α + 1) ^ 2 - (α + 1) * b + c)) (-α - 1) = 0 ∧
    cubic 1 b c ((α - j - 1) * ((α - j - 1) ^ 2 - (α - j - 1) * b + c))
      (-α + j + 1) = 0 := by
  constructor <;> unfold cubic <;> ring

def quarticDenominator (b c : K) : K :=
  (b - 3) * (c - 2 * b + 4) * (16 * c - 3 * b ^ 2 - 14 * b + 49)

/-- The rational certificate in (16), after the shifted common factor is removed. -/
theorem quartic_certificate (b c x : K) (h1 : x + 1 ≠ 0) (h2 : x + 2 ≠ 0) :
    cubic 1 b c (2 * c - 4 * b + 8) x * (-quarticNumerator b c x / (x + 2)) -
      cubic 1 b c 0 (x + 1) * (-quarticNumerator b c (x - 1) / (x + 1)) =
        quarticDenominator b c := by
  unfold cubic quarticNumerator quarticDenominator
  field_simp
  ring

/-- Equation (16), with its quartic numerator and rational prefactor. -/
theorem quartic_product_sum [CharZero K] (b c : K) (m : ℕ)
    (hD : quarticDenominator b c ≠ 0)
    (hv : ∀ j ≤ m, cubic 1 b c 0 (j + 1 : K) ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio (fun j => cubic 1 b c (2 * c - 4 * b + 8) (j : K))
        (fun j => cubic 1 b c 0 (j : K)) n /
        (cubic 1 b c 0 (n + 1 : K) * cubic 1 b c 0 (n + 2 : K)) =
      ((-quarticNumerator b c (m : K) / (m + 2 : K)) *
        productRatio (fun j => cubic 1 b c (2 * c - 4 * b + 8) (j : K))
          (fun j => cubic 1 b c 0 (j : K)) m / cubic 1 b c 0 (m + 1 : K) -
        (-quarticNumerator b c 0 / 2) / cubic 1 b c 0 1) / quarticDenominator b c := by
  have hF (n : ℕ) (_ : n < m) :
      cubic 1 b c (2 * c - 4 * b + 8) ((n + 1 : ℕ) : K) *
        (-quarticNumerator b c ((n + 1 : ℕ) : K) / (((n + 1 : ℕ) : K) + 2)) -
      cubic 1 b c 0 ((n + 2 : ℕ) : K) * (-quarticNumerator b c (n : K) / ((n : K) + 2)) =
        quarticDenominator b c := by
    have h1 : (n : K) + 1 + 1 ≠ 0 := by exact_mod_cast (show n + 1 + 1 ≠ 0 by omega)
    have h2 : (n : K) + 1 + 2 ≠ 0 := by exact_mod_cast (show n + 1 + 2 ≠ 0 by omega)
    convert quartic_certificate b c ((n : K) + 1) h1 h2 using 1
    push_cast
    ring_nf
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero, zero_add] using
    sum_product_certificate (fun j => cubic 1 b c (2 * c - 4 * b + 8) (j : K))
      (fun j => cubic 1 b c 0 (j : K)) (fun n => -quarticNumerator b c (n : K) / ((n : K) + 2))
      _ hD m (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hF

/-- The substitution following (16) generally makes the unreduced determinant nonzero. -/
theorem cubicMatrix_det_quartic (b c : K) :
    (cubicMatrix 1 b c (2 * c - 4 * b + 8) 0).det =
      4 * (2 * b - c - 4) * (b ^ 2 + 6 * (b - c) - 15) := by
  rw [cubicMatrix_det]
  ring

end Gosper
