module

public import SympyProofs.Gosper.Algorithm.Completeness
public meta import SympyProofs.Gosper.Algorithm.LinearElimination
public meta import SympyProofs.Gosper.Algorithm.LinearSolve
public meta import SympyProofs.Gosper.Algorithm.Polynomial

/-!
# Field-polynomial examples and matrix regressions

The matrix loop is executable with decidable field arithmetic. The polynomial
model uses Mathlib's noncomputable operations, so its examples are proved
symbolically rather than evaluated as dense-array programs.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm.Examples

open Polynomial

-- Row pivoting, a unique solution, free variables, and an inconsistent system.
#guard (solveLinear !![(0 : ℚ), 1; 1, 0] ![2, 3]).map
  (fun c => ![c 0, c 1]) == some ![3, 2]
#guard (solveLinear !![(1 : ℚ), 1; 1, -1] ![3, 1]).map
  (fun c => ![c 0, c 1]) == some ![2, 1]
#guard (solveLinear !![(1 : ℚ), 1; 2, 2] ![3, 6]).map
  (fun c => ![c 0, c 1]) == some ![3, 0]
#guard (solveLinear !![(1 : ℚ); 1] ![1, 2]).isNone
#guard (solveLinear (0 : Matrix (Fin 0) (Fin 2) ℚ) 0).map
  (fun c => ![c 0, c 1]) == some ![0, 0]
#guard (solveLinear (0 : Matrix (Fin 1) (Fin 0) ℚ) ![1]).isNone

variable {K : Type*} [Field K]

theorem geometric_certificate (r : K) (hr : r ≠ 1) :
    verify (C r) 1 1 (C (r - 1)) = true := by
  rw [verify_iff]
  refine ⟨one_ne_zero, Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hr), ?_⟩
  simp only [residual, taylor_one, taylor_C, map_sub, map_one]
  ring

theorem constant_term_certificate : verify (1 : K[X]) 1 X 1 = true := by
  rw [verify_iff]
  refine ⟨one_ne_zero, one_ne_zero, ?_⟩
  simp [residual, taylor_X]

theorem equal_constants_bound : degreeBound (1 : K[X]) 1 1 = 1 := by
  rw [degreeBound_eq_paper]
  norm_num [Gosper.paperDegreeBound]

variable [CharZero K]

theorem factorial_bound : degreeBound (X + 1 : K[X]) 1 1 = -1 := by
  rw [degreeBound_eq_paper]
  norm_num [Gosper.paperDegreeBound]

theorem exceptional_integer_bound : degreeBound (X - C 5 : K[X]) X 1 = 5 := by
  rw [degreeBound_eq_paper]
  norm_num [Gosper.paperDegreeBound]
  rw [Gosper.caseTwoDegreeBound_of_integer _ _ _ _ 5]
  · norm_num
  · norm_num [Gosper.exceptionalDegree]

theorem factorial_rejected : solvePolynomial (X + 1 : K[X]) 1 1 = none := by
  simp [solvePolynomial, factorial_bound]

/-- The complete pipeline finds an antidifference for the constant term. -/
theorem constant_term_accepted :
    ∃ c, gosperTerm (1 : K[X]) 1 = some c := by
  apply (gosperTerm_complete _ _ one_ne_zero one_ne_zero).mpr
  apply (forward_iff_hypergeometric _ (by simp [toRatFunc])).mp
  exact ⟨_, verify_ratFunc _ _ _ _ constant_term_certificate⟩

/-- The complete pipeline rejects n!: the normalized degree bound is negative. -/
theorem factorial_term_rejected : gosperTerm (X + 1 : K[X]) 1 = none := by
  have hP : (X + 1 : K[X]) ≠ 0 := by
    simpa using X_add_C_ne_zero (1 : K)
  let s : NormalForm K := ⟨X + 1, 1, 1, []⟩
  have hs : s.Valid (X + 1) 1 := by
    refine ⟨⟨hP, one_ne_zero, one_ne_zero⟩, ?_, ?_⟩
    · intro j
      simpa [s] using (isCoprime_one_right : IsCoprime (X + 1 : K[X]) 1)
    · simp [s]
  apply (gosperTerm_none_iff _ _ hP one_ne_zero).mpr
  rw [NormalForm.hypergeometric_iff_polynomial _ _ hP one_ne_zero s hs]
  have hn := (solvePolynomial_none_iff (X + 1 : K[X]) 1 1
    hP one_ne_zero one_ne_zero).mp factorial_rejected
  simpa [s] using hn

/-- Shift detection works over any characteristic-zero field, without choosing
a dense representation or restricting coefficients to ℚ. -/
theorem root_detection (j : ℕ) :
    j ∈ nonnegativeIntegerRoots (X - C (j : K)) := by
  rw [mem_nonnegativeIntegerRoots _ (X_sub_C_ne_zero _) j]
  simp

end Gosper.Algorithm.Examples
