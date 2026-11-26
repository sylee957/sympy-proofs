module

public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Lifts

/-! An algebraic extension of a differential field with algebraically closed constants introduces
no new constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial
open scoped Differential

variable {k F E : Type} [Field k] [IsAlgClosed k] [Field F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- An algebraic element has zero derivative precisely when it belongs to the constant field. -/
theorem algebraic_constant_iff (j : k →+* F) (hF : ∀ a : F, a′ = 0 ↔ a ∈ j.range)
    (x : E) (hx : IsIntegral F x) :
    x′ = 0 ↔ x ∈ ((algebraMap F E).comp j).range := by
  classical
  constructor
  · intro h
    let p := minpoly F x
    have hm : p.Monic := minpoly.monic hx
    have hev : aeval x p = 0 := minpoly.aeval F x
    have hdv : p ∣ Differential.mapCoeffs p := by
      apply minpoly.dvd F x
      have hd := Differential.deriv_aeval_eq x p
      simpa [hev, h] using hd.symm
    have hdeg : (Differential.mapCoeffs p).degree < p.degree := by
      rw [degree_eq_natDegree hm.ne_zero, degree_lt_iff_coeff_zero]
      intro i hi
      rw [Differential.coeff_mapCoeffs]
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · rw [coeff_natDegree, hm.leadingCoeff, Derivation.map_one_eq_zero]
      · rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
    have hz := eq_zero_of_dvd_of_degree_lt hdv hdeg
    obtain ⟨q,hq⟩ := (p.mem_lifts).mp <| (p.lifts_iff_coeff_lifts).mpr <| fun i =>
      (hF _).mp (by simpa using congrArg (fun s : F[X] => s.coeff i) hz)
    apply (IsAlgClosed.splits q).mem_range_of_isRoot
    · exact fun hq0 => hm.ne_zero (by simpa [hq0] using hq.symm)
    · rw [← map_map, hq, IsRoot, eval_map_algebraMap]
      exact hev
  · rintro ⟨c,rfl⟩
    change (algebraMap F E (j c))′ = 0
    rw [DifferentialAlgebra.deriv_algebraMap, (hF _).mpr ⟨c,rfl⟩, map_zero]

end SympyProofs.Calculus.Antiderivative.Elementary
