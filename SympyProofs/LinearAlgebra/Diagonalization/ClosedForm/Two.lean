module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Quadratic
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Meadow

/-!
# Diagonalization of 2 × 2 matrices by radicals

A single square root and total division construct both columns directly.
-/

@[expose] public section

noncomputable section

namespace SympyProofs.Diagonalization2

open Diagonalization Matrix

/-- Both quadratic roots, including the repeated root of a scalar or defective matrix. -/
def radicalRoots (A : Matrix (Fin 2) (Fin 2) ℂ) : List ℂ := quadraticRoots (-A.trace) A.det

theorem mem_radicalRoots (A : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    x ∈ radicalRoots A ↔ A.charpoly.eval x = 0 := by
  rw [radicalRoots, mem_quadraticRoots, charpoly_fin_two]
  simp [sub_eq_add_neg]

variable {K : Type*} [Field K]

def discriminant (A : Matrix (Fin 2) (Fin 2) K) : K := (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0

/-- The two columns share one denominator, including when the matrix is scalar. -/
def pair (A : Matrix (Fin 2) (Fin 2) K) (s : K) : Matrix (Fin 2) (Fin 2) K × (Fin 2 → K) :=
  let x := A 0 0 - A 1 1
  let u := (x + s) / 2
  let t := x + A 0 1 * A 1 0 / u
  (!![1, -A 0 1 / t; A 1 0 / t, 1], ![A 1 1 + t, A 0 0 - t])

private theorem discr_eq {A P : Matrix (Fin 2) (Fin 2) K}
    {d : Fin 2 → K} (h : IsDiagonalization A P d) :
    discriminant A = (d 0 - d 1) ^ 2 := by
  have hc := Meadow.charpoly_eq h
  have ht : A.trace = (diagonal d).trace := by
    rw [A.trace_eq_neg_charpoly_coeff, hc, ← Matrix.trace_eq_neg_charpoly_coeff]
  have hd : A.det = (diagonal d).det := by
    rw [A.det_eq_sign_charpoly_coeff, hc, ← Matrix.det_eq_sign_charpoly_coeff]
  simp [trace, Fin.sum_univ_two] at ht
  simp [det_fin_two] at hd
  unfold discriminant
  linear_combination (A 0 0 + A 1 1 + d 0 + d 1) * ht - 4 * hd

private theorem regular_or_scalar {A P : Matrix (Fin 2) (Fin 2) K}
    {d : Fin 2 → K} (h : IsDiagonalization A P d) :
    discriminant A ≠ 0 ∨ (A 0 0 = A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0) := by
  by_cases hd : d 0 = d 1
  · right
    have he : diagonal d = d 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, hd]
    have hA := h.2
    rw [he, Matrix.mul_smul, mul_one, Matrix.smul_mul,
      P.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h.1)] at hA
    simp [hA]
  · exact Or.inl (discr_eq h ▸ pow_ne_zero _ (sub_ne_zero.mpr hd))

private theorem pair_correct [CharZero K] (A : Matrix (Fin 2) (Fin 2) K)
    (s : K) (hs : s ^ 2 = discriminant A)
    (ok : discriminant A ≠ 0 ∨ (A 0 0 = A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0)) :
    IsDiagonalization A (pair A s).1 (pair A s).2 := by
  apply (Meadow.isDiagonalization_iff _ _ _).mpr
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, A = !![a, b; c, d] :=
    ⟨_, _, _, _, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  simp only [discriminant, pair, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at *
  rcases ok with hΔ | ⟨rfl, rfl, rfl⟩
  · let x := a - d
    let u := (x + s) / 2
    let t := x + b * c / u
    change s ^ 2 = x ^ 2 + 4 * b * c at hs
    have hu : u * (u - x) = b * c := by dsimp only [u]; linear_combination hs / 4
    have ht : t * (t - x) = b * c ∧ t ≠ 0 := by
      by_cases h : u = 0
      · have hbc : b * c = 0 := by simpa [h] using hu.symm
        have hx : x ≠ 0 := by
          intro hx
          apply hΔ
          change x ^ 2 + 4 * b * c=0
          rw [mul_assoc, hbc, hx]
          norm_num
        simpa [t, h, hbc] using hx
      · have te : t = u := by
          dsimp [t]
          field_simp
          linear_combination -hu
        exact ⟨te ▸ hu, te ▸ h⟩
    change (det (!![1, -b / t; c / t, 1] : Matrix (Fin 2) (Fin 2) K) ≠ 0) ∧
      !![a, b; c, d] * !![1, -b / t; c / t, 1] = !![1, -b / t; c / t, 1] * diagonal ![d + t, a - t]
    obtain ⟨ht, hn⟩ := ht
    constructor
    · have detval : det (!![1, -b / t; c / t, 1] : Matrix (Fin 2) (Fin 2) K) = (2 * t - x) / t := by
        simp [det_fin_two]
        field_simp
        linear_combination -ht
      rw [detval]
      apply div_ne_zero _ hn
      intro h
      apply hΔ
      change x ^ 2 + 4 * b * c=0
      linear_combination (2 * t - x) * h - 4 * ht
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal]
      all_goals field_simp
      all_goals dsimp only [x] at ht
      all_goals first | linear_combination ht | linear_combination -ht | ring
  · constructor
    · simp [det_fin_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal]

def complexPair (A : Matrix (Fin 2) (Fin 2) ℂ) := pair A (discriminant A).sqrt

def realPair (A : Matrix (Fin 2) (Fin 2) ℝ) := pair A (Real.sqrt (discriminant A))

theorem complexPair_correct (A : Matrix (Fin 2) (Fin 2) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (complexPair A).1 (complexPair A).2 := by
  obtain ⟨P, d, hd⟩ := h
  exact pair_correct A _ (Complex.cpow_nat_inv_pow _ (by decide)) (regular_or_scalar hd)

theorem realPair_correct (A : Matrix (Fin 2) (Fin 2) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realPair A).1 (realPair A).2 := by
  obtain ⟨P, d, hd⟩ := h
  exact pair_correct A _ (Real.sq_sqrt (discr_eq hd ▸ sq_nonneg _)) (regular_or_scalar hd)

/-- Return the direct complex eigenbasis when its certificate succeeds. -/
def diagonalizeComplex (A : Matrix (Fin 2) (Fin 2) ℂ) :=
  Meadow.asOption (Meadow.certify A (complexPair A))

theorem diagonalizeComplex_sound {A P : Matrix (Fin 2) (Fin 2) ℂ} {d : Fin 2 → ℂ}
    (h : diagonalizeComplex A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeComplex_isSome_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (diagonalizeComplex A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (complexPair_correct A)

/-- Return the direct real eigenbasis when its certificate succeeds. -/
def diagonalizeReal (A : Matrix (Fin 2) (Fin 2) ℝ) :=
  Meadow.asOption (Meadow.certify A (realPair A))

theorem diagonalizeReal_sound {A P : Matrix (Fin 2) (Fin 2) ℝ} {d : Fin 2 → ℝ}
    (h : diagonalizeReal A = some (P, d)) : IsDiagonalization A P d :=
  Meadow.asOption_sound h

theorem diagonalizeReal_isSome_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (diagonalizeReal A).isSome ↔ ∃ P d, IsDiagonalization A P d :=
  Meadow.asOption_isSome (realPair_correct A)

namespace StraightLine

/-- The direct complex diagonalization, with the zero pair encoding failure. -/
def formula (A : Matrix (Fin 2) (Fin 2) ℂ) := Meadow.certify A (complexPair A)

theorem formula_eq (A : Matrix (Fin 2) (Fin 2) ℂ) : formula A = (diagonalizeComplex A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem formula_correct (A : Matrix (Fin 2) (Fin 2) ℂ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (formula A).1 (formula A).2 :=
  Meadow.certify_correct (complexPair_correct A h)

theorem formula_eq_zero_of_defective (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : formula A = 0 :=
  Meadow.certify_eq_zero _ h

/-- The direct real diagonalization, with the zero pair encoding failure. -/
def realFormula (A : Matrix (Fin 2) (Fin 2) ℝ) := Meadow.certify A (realPair A)

theorem realFormula_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realFormula A = (diagonalizeReal A).getD 0 :=
  (Meadow.asOption_getD _ _).symm

theorem realFormula_correct (A : Matrix (Fin 2) (Fin 2) ℝ) (h : ∃ P d, IsDiagonalization A P d) :
    IsDiagonalization A (realFormula A).1 (realFormula A).2 :=
  Meadow.certify_correct (realPair_correct A h)

theorem realFormula_eq_zero_of_no_real_basis (A : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ¬ ∃ P d, IsDiagonalization A P d) : realFormula A = 0 :=
  Meadow.certify_eq_zero _ h

end StraightLine

end SympyProofs.Diagonalization2
