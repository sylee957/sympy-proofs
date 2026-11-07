module

public import Mathlib
meta import Mathlib

/-! Executable checks for Bareiss elimination with integer coefficient rows.
The harness divides row and right-hand-side updates by the previous pivot.
Its vector back substitution represents the polynomial accumulator used by `gosperSolve`. -/

namespace Gosper.Algorithm.EliminationExamples

/-- A test-only harness for Bareiss elimination and vector back substitution. -/
private def runInline {K L : Type} [CommRing K] [DecidableEq K] [Div K]
    [CommRing L] [Algebra K L] [Div L] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → L) : K × (Fin n → L) := Id.run do
  let mut M := Vector.ofFn fun i : Fin m => Vector.ofFn (A i)
  let mut rhs := Vector.ofFn b
  let mut pivots : List (Fin n × K × Vector K n × L) := []
  let mut previousPivot := (1 : K)
  -- Eliminate columns using pivots from K, retaining each pivot equation.
  for col in List.finRange n do
    let mut pivot : Option (Fin m) := none
    for i in List.finRange m do
      if M[i.val][col.val] ≠ 0 then
        pivot := some i
        break
    if let some i := pivot then
      let row := M[i.val]
      let p := row[col.val]
      let value := rhs[i.val]
      pivots := (col, p, row, value) :: pivots
      for i in List.finRange m do
        let source := M[i.val]
        let a := source[col.val]
        rhs := rhs.set i.val
          ((algebraMap K L p * rhs[i.val] - algebraMap K L a * value) /
            algebraMap K L previousPivot)
        let mut updated := source
        for k in List.finRange n do
          updated := updated.set k.val ((p * source[k.val] - a * row[k.val]) / previousPivot)
        M := M.set i.val updated
      previousPivot := p
  -- The stored equations are already ordered for back-substitution.
  let mut δ := (1 : K)
  let mut coefficients := Vector.replicate n (0 : L)
  for (col, p, row, pivotRhs) in pivots do
    let mut value := (0 : L)
    for k in List.finRange n do
      value := value + algebraMap K L row[k.val] * coefficients[k.val]
    value := algebraMap K L δ * pivotRhs - value
    coefficients := coefficients.map fun a => algebraMap K L p * a
    coefficients := coefficients.set col.val (coefficients[col.val] + value)
    δ := p * δ
  return (δ, fun j => coefficients[j.val])

/-- With no equations every variable is free and is set to zero. -/
def zero_rows : Bool := decide (
    runInline (0 : Matrix (Fin 0) (Fin 2) ℤ) (0 : Fin 0 → ℚ) = (1, ![0, 0]))

/-- With no unknowns the denominator is still one, even for an inconsistent RHS. -/
def zero_columns : Bool := decide (
    runInline (0 : Matrix (Fin 2) (Fin 0) ℤ) (![1, 0] : Fin 2 → ℚ) =
      (1, Fin.elim0))

/-- The first column is free; the next pivot requires a denominator of two. -/
def skipped_column : Bool := decide (
    runInline (!![0, 2; 0, 4] : Matrix (Fin 2) (Fin 2) ℤ)
      (![3, 6] : Fin 2 → ℚ) = (2, ![0, 3]))

/-- Dependent equations leave the second variable free. -/
def rank_deficient_consistent : Bool := decide (
    runInline (!![1, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ)
      (![3, 6] : Fin 2 → ℚ) = (1, ![3, 0]))

/-- Inconsistency is retained in the original equations' residual. -/
def inconsistent_residual : Bool := decide (
    let M : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 2, 2]
    let b : Fin 2 → ℚ := ![1, 3]
    let result := runInline M b
    algebraMap ℤ ℚ result.1 • b - (M.map (algebraMap ℤ ℚ)).mulVec result.2 = ![0, 1])

/-- Nonunit pivots retain a common denominator while row divisions are exact. -/
def nonunit_pivots : Bool := decide (
    runInline (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℤ)
      (![1, 2] : Fin 2 → ℚ) = (10, ![2, 6]))

/-- Dividing the third pivot update by two reduces the returned scale from
720 (without Bareiss division) to 360. The right-hand side also stays integral. -/
def third_pivot_exact_division : Bool := decide (
    runInline (!![2, 0, 0; 0, 3, 0; 0, 0, 5] : Matrix (Fin 3) (Fin 3) ℤ)
      (![2, 6, 15] : Fin 3 → ℤ) = (360, ![360, 720, 1080]))

/-- Skipped columns preserve the previous pivot. Three pivot columns and a
dependent equation still produce the reduced scale, with free coefficients zero. -/
def skipped_columns_rank_deficient : Bool := decide (
    runInline (!![2, 0, 0, 0, 0; 0, 0, 3, 0, 0; 0, 0, 0, 0, 5; 2, 0, 3, 0, 5] :
      Matrix (Fin 4) (Fin 5) ℤ)
      (![2, 6, 15, 23] : Fin 4 → ℤ) = (360, ![360, 0, 720, 0, 1080]))

/-- An inconsistent dependent equation remains visible after three exact pivots,
including the skipped columns between them. -/
def inconsistent_after_three_pivots : Bool := decide (
    let M : Matrix (Fin 4) (Fin 5) ℤ :=
      !![2, 0, 0, 0, 0; 0, 0, 3, 0, 0; 0, 0, 0, 0, 5; 2, 0, 3, 0, 5]
    let b : Fin 4 → ℤ := ![2, 6, 15, 24]
    let result := runInline M b
    result = (360, ![360, 0, 720, 0, 1080]) ∧
      result.1 • b - M.mulVec result.2 = ![0, 0, 0, 360])

/-- The first pivot is on a later row; rectangular zero rows stay harmless. -/
def later_pivot_row : Bool := decide (
    runInline (!![0, 2; 0, 0; 3, 1] : Matrix (Fin 3) (Fin 2) ℤ)
      (![4, 0, 5] : Fin 3 → ℚ) = (18, ![18, 36]))

/-- A runtime-only check of division by diagonal rational scalars.
`ℚ × ℚ` has componentwise division but does not satisfy the full
`MulDivCancelClass` interface used by the correctness theorem. -/
def product_rhs : Bool := decide (
    runInline (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℤ)
      (![(1, 2), (2, 1)] : Fin 2 → ℚ × ℚ) = (10, ![(2, 10), (6, 0)]))

/-- For `A=X²`, `B=X²+X+1`, the columns of `A*x(X+1)-B*x` for
`x=1,X` are `(-1,-1,0)` and `(0,-1,0)`. The output represents `x=X-1`. -/
def exceptional_gosper : Bool := decide (
    runInline (!![-1, 0; -1, -1; 0, 0] : Matrix (Fin 3) (Fin 2) ℤ)
      (![1, 0, 0] : Fin 3 → ℚ) = (-1, ![1, -1]))

/-- A moderate system detects repeated evaluation of nested elimination closures. -/
def identity_moderate : Bool := decide (
    let b : Fin 12 → ℚ := fun i => (i.val : ℚ) + 1
    runInline (1 : Matrix (Fin 12) (Fin 12) ℤ) b = (1, b))

-- These checks run the Bareiss reference implementation. A mismatch is a build error.
#eval show IO Unit from do
  let checks := [
    ("zero_rows", zero_rows),
    ("zero_columns", zero_columns),
    ("skipped_column", skipped_column),
    ("rank_deficient_consistent", rank_deficient_consistent),
    ("inconsistent_residual", inconsistent_residual),
    ("nonunit_pivots", nonunit_pivots),
    ("third_pivot_exact_division", third_pivot_exact_division),
    ("skipped_columns_rank_deficient", skipped_columns_rank_deficient),
    ("inconsistent_after_three_pivots", inconsistent_after_three_pivots),
    ("later_pivot_row", later_pivot_row),
    ("product_rhs", product_rhs),
    ("exceptional_gosper", exceptional_gosper),
    ("identity_moderate", identity_moderate)]
  for (name, passed) in checks do
    unless passed do
      throw (IO.userError s!"Bareiss elimination regression failed: {name}")

end Gosper.Algorithm.EliminationExamples
