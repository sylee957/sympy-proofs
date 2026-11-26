module

public import SympyProofs.Calculus.Antiderivative.Algebra.TangentUnit
public import SympyProofs.Calculus.Antiderivative.Spec.Factor
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.LinearCombination

/-! Effective decision and witness for a square root of negative one in the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

open Polynomial

variable (F : Type) [Field F] [DecidableEq F] [ConstantFactors F] [LawfulConstantFactors F]

/-- Factoring the defining quadratic recovers a square root whenever one exists. -/
theorem tangentUnit_sq (h : IsSquare (-1 : F)) : tangentUnit F ^ 2 = -1 := by
  obtain ⟨r,hr⟩ := h
  let p := (Poly.X^2 + 1 : Poly F)
  have he : Poly.equiv p = X^2 + C 1 := by simp [p]
  have hm : (Poly.equiv p).Monic := he ▸ monic_X_pow_add_C _ (by decide)
  have hn : p ≠ 0 := fun hz => hm.ne_zero (by rw [hz,map_zero])
  have hs : (Poly.equiv p).Splits := by
    have eq : Poly.equiv p = (X-C r)*(X-C (-r)) := by
      rw [he,map_neg,sub_neg_eq_add,map_one]
      have hh := congrArg (C : F → F[X]) hr
      simp only [map_neg,map_one,map_mul] at hh
      linear_combination -hh
    rw [eq]
    exact (Splits.X_sub_C r).mul (Splits.X_sub_C (-r))
  have hl : p.leadingCoeff = 1 := by simpa using hm.leadingCoeff
  have prod := LawfulConstantFactors.product p hn
  rw [hl,Poly.C_one,one_mul] at prod
  cases hfs : ConstantFactors.factors p with
  | nil =>
    rw [hfs,List.prod_nil] at prod
    have hd := congrArg (fun q : Poly F => (Poly.equiv q).natDegree) prod
    simp [he] at hd
  | cons f fs =>
    obtain ⟨mon,irr⟩ := LawfulConstantFactors.irreducible p hn f (by simp [hfs])
    have hd : f ∣ p := ⟨fs.prod,by simpa [hfs] using prod.symm⟩
    have ed := map_dvd Poly.equiv hd
    have ir : Irreducible (Poly.equiv f) := (MulEquiv.irreducible_iff (Poly.equiv (R := F))).mpr irr
    have degree := (hs.of_dvd hm.ne_zero ed).natDegree_eq_one_of_irreducible ir
    have fr : (Poly.equiv f).IsRoot (-f.coeff 0) := by
      rw [mon.eq_X_add_C degree,IsRoot.def]
      simp
    have pr : (Poly.equiv p).IsRoot (-f.coeff 0) := dvd_iff_isRoot.mp
      ((dvd_iff_isRoot.mpr fr).trans ed)
    change (-((ConstantFactors.factors p).headD 0).coeff 0)^2 = -1
    rw [hfs,List.headD_cons]
    rw [he,IsRoot.def] at pr
    simpa using eq_neg_of_add_eq_zero_left (by simpa using pr)

/-- The factorization test decides whether to use an existing unit or to adjoin one. -/
instance (priority := low) decidableNegOneSquare : Decidable (IsSquare (-1 : F)) :=
  decidable_of_iff (tangentUnit F ^ 2 = -1)
    ⟨fun h => ⟨tangentUnit F,by simpa [pow_two] using h.symm⟩,tangentUnit_sq F⟩

end SympyProofs.Calculus.Antiderivative.Trigonometric
