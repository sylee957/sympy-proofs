module

public import SympyProofs.Gosper.Algorithm.Polynomial
public import SympyProofs.Gosper.Degree

/-! The paper's signed degree bound over a characteristic-zero field. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K]

local instance degreeDecidableEq : DecidableEq K := Classical.decEq K

/-- Bound for A(X)x(X+1) - B(X)x(X) = C(X). Testing coefficients at the
maximum degree combines SymPy's unequal-degree / unequal-leading-term cases.
The exceptional integer root is retained even when negative. -/
def degreeBound (A B C : K[X]) : ℤ := Id.run do
  let l := max A.natDegree B.natDegree
  if A.coeff l ≠ B.coeff l then return (C.natDegree : ℤ) - l
  if l = 0 then return (C.natDegree : ℤ) + 1
  let ordinary := (C.natDegree : ℤ) - l + 1
  let exceptional := (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l
  match integerValue exceptional with
  | some k => return max k ordinary
  | none => return ordinary

theorem degreeBound_eq_paper (A B C : K[X]) :
    degreeBound A B C = Gosper.paperDegreeBound C A B := by
  classical
  simp only [degreeBound, Id.run, pure, Gosper.paperDegreeBound]
  split_ifs <;> simp_all [Gosper.caseTwoDegreeBound, integerValue, Gosper.exceptionalDegree]
  split_ifs <;> rfl

/-- Reuse the proved paper bound: translate x forward to turn the forward
equation into the paper's backward equation; translation preserves degree. -/
theorem solution_degree_le [CharZero K] (A B C x : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A * taylor 1 x - B * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound A B C := by
  rw [degreeBound_eq_paper]
  have ht : taylor (1 : K) x ≠ 0 := (taylor_eq_zero _ _).not.mpr hx
  have he' : A * taylor 1 x - B * taylor (-1) (taylor 1 x) = C := by
    simpa [taylor_taylor] using he
  simpa using Gosper.solution_intDegree_le C A B (taylor 1 x) hA hB ht he'

end Gosper.Algorithm
