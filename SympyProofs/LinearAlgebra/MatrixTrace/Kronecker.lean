module

public import SympyProofs.LinearAlgebra.MatrixTrace.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Traces of Kronecker products with rectangular factors.

Rows and columns are flattened separately in row-major order. When `m * p = n * q`,
the resulting matrix is square, even if its factors are rectangular. Its diagonal
is computed using quotient and remainder with respect to the second factor's row
and column counts. For square factors, trace simplifies to a product of traces;
rectangular diagonal sums do not satisfy that identity in general.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker

variable {R : Type*} {m n p q : ℕ}

/-- A Kronecker product with row-major finite indices instead of pairs of indices. -/
def kroneckerFin [Mul R] (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin p) (Fin q) R) : Matrix (Fin (m * p)) (Fin (n * q)) R :=
  reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

@[simp]
theorem kroneckerFin_apply [Mul R] (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin p) (Fin q) R) (i : Fin (m * p)) (j : Fin (n * q)) :
    kroneckerFin A B i j = A i.divNat j.divNat * B i.modNat j.modNat :=
  rfl

/-- Compute the diagonal sum directly, without forming the full Kronecker matrix.
The formula also covers rectangular products and zero dimensions. -/
theorem diagonalSum_kroneckerFin [AddCommMonoid R] [Mul R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R) :
    diagonalSum (kroneckerFin A B) =
      ∑ k : Fin (min (m * p) (n * q)),
        A (k.castLE (Nat.min_le_left _ _)).divNat
            (k.castLE (Nat.min_le_right _ _)).divNat *
          B (k.castLE (Nat.min_le_left _ _)).modNat
            (k.castLE (Nat.min_le_right _ _)).modNat :=
  rfl

/-- The trace of a square Kronecker product of possibly rectangular factors.
Here `divNat` and `modNat` are the quotient and remainder of the flat index;
the equality of total dimensions identifies column and row indices. -/
theorem trace_kroneckerFin_of_mul_eq_mul [AddCommMonoid R] [Mul R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast h)) =
      ∑ k : Fin (m * p),
        A k.divNat (k.cast h).divNat * B k.modNat (k.cast h).modNat :=
  rfl

/-- The diagonal-sum version of the trace formula when total dimensions agree. -/
theorem diagonalSum_kroneckerFin_of_mul_eq_mul [AddCommMonoid R] [Mul R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    diagonalSum (kroneckerFin A B) =
      ∑ k : Fin (m * p),
        A k.divNat (k.cast h).divNat * B k.modNat (k.cast h).modNat := by
  rw [← trace_submatrix_cast_eq_diagonalSum (kroneckerFin A B) h]
  exact trace_kroneckerFin_of_mul_eq_mul A B h

/-- Express the trace using ordinary natural-number division and remainder.
Each index is constructed as `⟨value, bounds proof⟩`, so the formula uses
ordinary matrix application. The cast on the left only identifies dimensions. -/
theorem trace_kroneckerFin_eq_sum_div_mod [AddCommMonoid R] [Mul R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast h)) =
      ∑ k : Fin (m * p),
        A ⟨k.val / p, k.divNat.is_lt⟩
            ⟨k.val / q, Nat.div_lt_of_lt_mul (by
              simpa only [Nat.mul_comm q n, ← h] using k.is_lt)⟩ *
          B ⟨k.val % p, k.modNat.is_lt⟩
            ⟨k.val % q, Nat.mod_lt _
              (Nat.pos_of_mul_pos_left (h ▸ Nat.zero_lt_of_lt k.is_lt))⟩ :=
  rfl

/-- A cast-free statement of the trace formula when total dimensions agree.
Here `diagonalSum` agrees with the ordinary trace after identifying dimensions. -/
theorem diagonalSum_kroneckerFin_eq_sum_div_mod [AddCommMonoid R] [Mul R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (h : m * p = n * q) :
    diagonalSum (kroneckerFin A B) =
      ∑ k : Fin (m * p),
        A ⟨k.val / p, k.divNat.is_lt⟩
            ⟨k.val / q, Nat.div_lt_of_lt_mul (by
              simpa only [Nat.mul_comm q n, ← h] using k.is_lt)⟩ *
          B ⟨k.val % p, k.modNat.is_lt⟩
            ⟨k.val % q, Nat.mod_lt _
              (Nat.pos_of_mul_pos_left (h ▸ Nat.zero_lt_of_lt k.is_lt))⟩ := by
  rw [← trace_submatrix_cast_eq_diagonalSum (kroneckerFin A B) h]
  exact trace_kroneckerFin_eq_sum_div_mod A B h

/-- For square factors, the row-major trace agrees with the usual Kronecker
product-of-traces identity. -/
@[simp]
theorem trace_kroneckerFin [Semiring R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin p) (Fin p) R) :
    trace (kroneckerFin A B) = trace A * trace B := by
  rw [kroneckerFin, trace_reindex, trace_kronecker]

/-- Factor the trace when each factor is square after identifying equal dimensions.
The factors can themselves be Kronecker products of rectangular matrices. -/
theorem trace_kroneckerFin_of_eq [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (hA : m = n) (hB : p = q) :
    trace ((kroneckerFin A B).submatrix id (Fin.cast (congrArg₂ Nat.mul hA hB))) =
      trace (A.submatrix id (Fin.cast hA)) * trace (B.submatrix id (Fin.cast hB)) := by
  subst n
  subst q
  simp

/-- Split four factors into two consecutive square groups, preserving their order. -/
theorem trace_kroneckerFin_group_pairs [Semiring R] {a b c d : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R)
    (C : Matrix (Fin a) (Fin b) R) (D : Matrix (Fin c) (Fin d) R)
    (hAB : m * p = n * q) (hCD : a * c = b * d) :
    trace ((kroneckerFin (kroneckerFin A B) (kroneckerFin C D)).submatrix id
      (Fin.cast (congrArg₂ Nat.mul hAB hCD))) =
      trace ((kroneckerFin A B).submatrix id (Fin.cast hAB)) *
        trace ((kroneckerFin C D).submatrix id (Fin.cast hCD)) :=
  trace_kroneckerFin_of_eq (kroneckerFin A B) (kroneckerFin C D) hAB hCD

end Matrix
