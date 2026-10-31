module

public import SympyProofs.Sum.Gosper.Algorithm.Polynomial
public import SympyProofs.Sum.Gosper.Degree

/-! The paper's signed degree bound over a characteristic-zero field. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- Bound for A(X)x(X+1) - B(X)x(X) = C(X). Testing coefficients at the
maximum degree combines SymPy's unequal-degree / unequal-leading-term cases.
The exceptional integer root is retained even when negative. -/
def degreeBound {L : Type*} [Semiring L] (A B : K[X]) (C : L[X]) : ℤ := Id.run do
  let l := max A.natDegree B.natDegree
  if A.coeff l ≠ B.coeff l then return (C.natDegree : ℤ) - l
  if l = 0 then return (C.natDegree : ℤ) + 1
  let ordinary := (C.natDegree : ℤ) - l + 1
  let exceptional := (B.coeff (l - 1) - A.coeff (l - 1)) / B.coeff l
  if h : IsInteger ℤ exceptional then
    let k : ℤ := Encodable.choose h
    return max k ordinary
  return ordinary

theorem degreeBound_eq_paper (A B C : K[X]) :
    degreeBound A B C = Gosper.paperDegreeBound C A B := by
  classical
  simp only [degreeBound, Id.run, pure, Gosper.paperDegreeBound]
  split_ifs with hc hl hi
  · rfl
  · rfl
  · exact (Gosper.caseTwoDegreeBound_of_integer C A B _ (Encodable.choose hi)
      (Encodable.choose_spec hi)).symm
  · exact (Gosper.caseTwoDegreeBound_of_not_integer C A B _ hi).symm

/-- Reuse the proved paper bound: translate x forward to turn the forward
equation into the paper's backward equation; translation preserves degree. -/
theorem solution_degree_le (A B C x : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A * taylor 1 x - B * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound A B C := by
  rw [degreeBound_eq_paper]
  have ht : taylor (1 : K) x ≠ 0 := (taylor_eq_zero _ _).not.mpr hx
  have he' : A * taylor 1 x - B * taylor (-1) (taylor 1 x) = C := by
    simpa [taylor_taylor] using he
  simpa using Gosper.solution_intDegree_le C A B (taylor 1 x) hA hB ht he'

section Extension

variable {L : Type*} [Field L] [CharZero L] [Algebra K L]
  [DecidableEq L] [DecidablePred (IsInteger ℤ : L → Prop)]

/-- Extending the coefficient field does not change the degree bound: its only
dependence on the right-hand side is its degree. -/
theorem degreeBound_map (A B : K[X]) (C : L[X]) :
    degreeBound (A.map (algebraMap K L)) (B.map (algebraMap K L)) C =
      degreeBound A B C := by
  have hint (x : K) : IsInteger ℤ (algebraMap K L x) ↔ IsInteger ℤ x := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, (algebraMap K L).injective ?_⟩
      simpa using hz
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa using congrArg (algebraMap K L) hz
  have hne (a b : K) : algebraMap K L a ≠ algebraMap K L b ↔ a ≠ b :=
    not_congr (algebraMap K L).injective.eq_iff
  simp only [degreeBound, Id.run, pure,
    Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
    coeff_map, ← map_sub, ← map_div₀, hne]
  split_ifs with hc hl hL hK hK
  · rfl
  · rfl
  · congr 1
    apply Int.cast_injective (α := K)
    apply (algebraMap K L).injective
    simpa using
      (Encodable.choose_spec hL).trans (congrArg (algebraMap K L) (Encodable.choose_spec hK)).symm
  · exact (hK ((hint _).mp hL)).elim
  · exact (hL ((hint _).mpr hK)).elim
  · rfl

omit [CharZero L] [DecidableEq L] [DecidablePred (IsInteger ℤ : L → Prop)] in
/-- The bound computed in `K` applies to solutions with coefficients in `L`. -/
theorem solution_degree_le_extension (A B : K[X]) (C x : L[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound A B C := by
  classical
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  rw [← degreeBound_map A B C]
  apply solution_degree_le _ _ _ _ _ _ hx he
  · simpa using hA
  · simpa using hB

end Extension

end Gosper.Algorithm
