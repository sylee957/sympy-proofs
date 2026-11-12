module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Diagonal sums of rectangular matrices with ordered finite indices.

`Matrix.diagonalSum` sums the first `min m n` diagonal entries. This is a
coordinate-dependent extension of trace to rectangular arrays, not the trace of
a linear endomorphism. On square matrices it agrees with `Matrix.trace`.
-/

@[expose] public section

namespace Matrix

variable {R S : Type*} {m n : ℕ}

/-- The sum of the diagonal entries present in a rectangular matrix. -/
def diagonalSum [AddCommMonoid R] (A : Matrix (Fin m) (Fin n) R) : R :=
  ∑ i : Fin (min m n), A (i.castLE (Nat.min_le_left m n)) (i.castLE (Nat.min_le_right m n))

@[simp]
theorem diagonalSum_eq_trace [AddCommMonoid R] (A : Matrix (Fin n) (Fin n) R) :
    diagonalSum A = trace A :=
  (finCongr (min_self n)).sum_comp (fun i => A i i)

@[simp]
theorem diagonalSum_zero [AddCommMonoid R] :
    diagonalSum (0 : Matrix (Fin m) (Fin n) R) = 0 := by
  simp [diagonalSum]

@[simp]
theorem diagonalSum_zero_rows [AddCommMonoid R] (A : Matrix (Fin 0) (Fin n) R) :
    diagonalSum A = 0 := by
  simp [diagonalSum]

@[simp]
theorem diagonalSum_zero_cols [AddCommMonoid R] (A : Matrix (Fin m) (Fin 0) R) :
    diagonalSum A = 0 := by
  simp [diagonalSum]

@[simp]
theorem diagonalSum_add [AddCommMonoid R] (A B : Matrix (Fin m) (Fin n) R) :
    diagonalSum (A + B) = diagonalSum A + diagonalSum B := by
  simp [diagonalSum, Finset.sum_add_distrib]

@[simp]
theorem diagonalSum_smul [AddCommMonoid R] [DistribSMul S R]
    (c : S) (A : Matrix (Fin m) (Fin n) R) :
    diagonalSum (c • A) = c • diagonalSum A := by
  simp [diagonalSum, Finset.smul_sum]

@[simp]
theorem diagonalSum_transpose [AddCommMonoid R] (A : Matrix (Fin m) (Fin n) R) :
    diagonalSum Aᵀ = diagonalSum A := by
  unfold diagonalSum
  rw [← (finCongr (Nat.min_comm m n)).sum_comp]
  rfl

/-- Reindexing the rows and columns by the same equivalence preserves trace. -/
@[simp]
theorem trace_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (e : ι ≃ κ) (A : Matrix ι ι R) :
    trace (reindex e e A) = trace A :=
  e.symm.sum_comp (fun i => A i i)

/-- When the dimensions agree, identifying the column indices with the row
indices turns the diagonal sum into an ordinary trace. -/
theorem trace_submatrix_cast_eq_diagonalSum [AddCommMonoid R]
    (A : Matrix (Fin m) (Fin n) R) (h : m = n) :
    trace (A.submatrix id (Fin.cast h)) = diagonalSum A := by
  subst n
  simp

end Matrix
