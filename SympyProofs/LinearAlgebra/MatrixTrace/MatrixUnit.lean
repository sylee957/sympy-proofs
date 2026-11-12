module

public import SympyProofs.LinearAlgebra.MatrixTrace.Kronecker

/-! Traces of matrix units, represented by `Matrix.single i j 1`.

The weighted formulas allow an arbitrary entry in place of `1`. Indices belong
to the matrix's row and column types, so their validity is guaranteed. The
integer-indexed extension with explicit bounds is in `MatrixUnitBounds`.
-/

@[expose] public section

namespace Matrix

variable {R ι κ : Type*}

/-- The trace of a weighted matrix unit is its weight on the diagonal and zero
off the diagonal. This is the Kronecker-delta trace formula. -/
theorem trace_single [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (i j : ι) (a : R) : trace (single i j a) = if i = j then a else 0 := by
  by_cases h : i = j <;> simp [h]

/-- Left multiplication by a matrix unit extracts the transposed entry under trace.
The matrix unit and the other factor can both be rectangular. -/
@[simp]
theorem trace_single_one_mul [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [NonAssocSemiring R] (i : ι) (j : κ) (A : Matrix κ ι R) :
    trace (single i j (1 : R) * A) = A j i := by
  simp [trace_single_mul]

/-- Right multiplication by a matrix unit extracts the same transposed entry. -/
@[simp]
theorem trace_mul_single_one [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [NonAssocSemiring R] (i : ι) (j : κ) (A : Matrix κ ι R) :
    trace (A * single i j (1 : R)) = A j i := by
  simp [trace_mul_single]

/-- The weighted form of `trace (Eᵢⱼ * Eₖₗ) = δⱼₖ δᵢₗ`. -/
theorem trace_single_mul_single [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [NonUnitalNonAssocSemiring R] (i l : ι) (j k : κ) (a b : R) :
    trace (single i j a * single k l b) = if j = k ∧ i = l then a * b else 0 := by
  simp only [trace_single_mul, single_apply, smul_eq_mul]
  simp only [show (k = j ∧ l = i) ↔ (j = k ∧ i = l) from and_congr eq_comm eq_comm,
    mul_ite, mul_zero]

/-- The diagonal-sum extension for a rectangular weighted matrix unit. -/
theorem diagonalSum_single [AddCommMonoid R] {m n : ℕ}
    (i : Fin m) (j : Fin n) (a : R) :
    diagonalSum (single i j a) = if i.val = j.val then a else 0 := by
  classical
  by_cases h : i.val = j.val
  · have hi : i.val < min m n := lt_min i.is_lt (h ▸ j.is_lt)
    let k : Fin (min m n) := ⟨i.val, hi⟩
    rw [ite_eq_left h, diagonalSum, Finset.sum_eq_single k]
    · have hk₁ : k.castLE (Nat.min_le_left m n) = i := Fin.ext rfl
      have hk₂ : k.castLE (Nat.min_le_right m n) = j := Fin.ext h
      simp [hk₁, hk₂]
    · intro l _ hl
      apply single_apply_of_row_ne
      intro hil
      apply hl
      apply Fin.ext
      exact (congrArg Fin.val hil).symm
    · simp
  · rw [ite_eq_right h, diagonalSum]
    apply Finset.sum_eq_zero
    intro k _
    apply single_apply_of_ne
    intro hk
    exact h ((congrArg Fin.val hk.1).trans (congrArg Fin.val hk.2).symm)

/-- Row-major Kronecker products of weighted matrix units are weighted matrix units. -/
theorem kroneckerFin_single_single [MulZeroClass R] {m n p q : ℕ}
    (i : Fin m) (j : Fin n) (k : Fin p) (l : Fin q) (a b : R) :
    kroneckerFin (single i j a) (single k l b) =
      single (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) (a * b) := by
  simp only [kroneckerFin, single_kronecker_single, reindex_apply,
    submatrix_single_equiv, Equiv.symm_symm]

/-- Equal dimensions identify the two finite index types without changing the
integer-coordinate test for a diagonal entry. -/
theorem trace_single_submatrix_cast [AddCommMonoid R] {m n : ℕ}
    (i : Fin m) (j : Fin n) (a : R) (h : m = n) :
    trace ((single i j a).submatrix id (Fin.cast h)) =
      if i.val = j.val then a else 0 := by
  subst n
  simp [trace_single, Fin.ext_iff]

/-- For rectangular matrix units with a square Kronecker product, the trace tests
equality of the flattened indices `i*p + k` and `j*q + l`. -/
theorem trace_kroneckerFin_single_single [NonUnitalNonAssocSemiring R]
    {m n p q : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) (l : Fin q) (a b : R)
    (h : m * p = n * q) :
    trace ((kroneckerFin (single i j a) (single k l b)).submatrix id (Fin.cast h)) =
      if i.val * p + k.val = j.val * q + l.val then a * b else 0 := by
  rw [kroneckerFin_single_single, trace_single_submatrix_cast]
  simp only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]

end Matrix
