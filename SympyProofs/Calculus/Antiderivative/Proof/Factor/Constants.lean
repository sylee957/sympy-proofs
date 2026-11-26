module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Rational

/-! Transport factorization through the constant-field isomorphism at height zero. -/

public section

namespace SympyProofs.Calculus.Antiderivative

namespace ConstantFactors

variable {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]

/-- Transport polynomial coefficients through a field isomorphism. -/
private noncomputable def polys (e : F ≃+* G) : Poly F ≃+* Poly G :=
  Poly.equiv.trans ((Polynomial.mapEquiv e).trans Poly.equiv.symm)

private theorem polys_apply (e : F ≃+* G) (p : Poly F) : polys e p = p.map e := by
  apply Poly.equiv.injective
  change Poly.equiv (Poly.equiv.symm (_ : Polynomial G)) = _
  rw [RingEquiv.apply_symm_apply]
  exact (Poly.equiv_map e.toRingHom p).symm

private theorem equiv_map (e : F ≃+* G) (p : Poly F) :
    Poly.equiv (p.map e) = (Poly.equiv p).map e.toRingHom := Poly.equiv_map e.toRingHom p

private theorem polys_symm_apply (e : F ≃+* G) (p : Poly G) : (polys e).symm p = p.map e.symm :=
  polys_apply e.symm p

/-- An executable pair of mutually inverse coefficient conversions preserves factorization. -/
theorem lawfulOfMaps [ConstantFactors G] [LawfulConstantFactors G] (e : F ≃+* G)
    (g : G → F) (hg : g = e.symm) :
    letI := ofMaps (e : F → G) g
    LawfulConstantFactors F := by
  subst g
  let _ := ofMaps (e : F → G) (e.symm : G → F)
  refine LawfulConstantFactors.mk ?_ ?_
  · intro p hp q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    have hn : p.map e ≠ 0 := by
      rw [← polys_apply]
      exact (map_ne_zero_iff _ (polys e).injective).mpr hp
    obtain ⟨hm, hi⟩ := LawfulConstantFactors.irreducible (p.map e) hn b hb
    refine ⟨?_, ?_⟩
    · rw [equiv_map e.symm]
      exact hm.map _
    · rw [← polys_symm_apply]
      exact hi.map _
  · intro p hp
    have hn := (map_ne_zero_iff (polys e) (polys e).injective).mpr hp
    have law := congrArg ((polys e).symm) (LawfulConstantFactors.product (polys e p) hn)
    rw [RingEquiv.symm_apply_apply, map_mul, map_list_prod] at law
    have lead : (polys e p).leadingCoeff = e p.leadingCoeff := by
      rw [polys_apply, ← Poly.leadingCoeff_equiv, equiv_map e,
        Polynomial.leadingCoeff_map_of_injective e.injective, Poly.leadingCoeff_equiv]
      rfl
    have hc : (polys e).symm (Poly.C (e p.leadingCoeff)) = Poly.C p.leadingCoeff := by
      rw [polys_symm_apply]
      apply Poly.equiv.injective
      rw [equiv_map e.symm, Poly.equiv_C, Polynomial.map_C, Poly.equiv_C]
      simp
    rw [lead, hc, polys_apply] at law
    change Poly.C p.leadingCoeff * ((ConstantFactors.factors (p.map e)).map _).prod = p
    rw [← (show (⇑(polys e).symm) = Poly.map e.symm from funext (polys_symm_apply e))]
    exact law

end ConstantFactors

/-- The height-zero fraction field of the integers inherits verified rational factorization. -/
instance : LawfulConstantFactors (K ℤ 0) :=
  ConstantFactors.lawfulOfMaps (K.constantsEquiv ℚ) _ (by
    funext c
    exact (K.constantsEquiv ℚ).symm_apply_eq.mpr (by simp) |>.symm)

/-- The height-zero fraction field of a field inherits its verified factorization. -/
instance {F : Type} [Field F] [DecidableEq F] [ConstantFactors F] [LawfulConstantFactors F] :
    LawfulConstantFactors (K F 0) :=
  ConstantFactors.lawfulOfMaps (K.constantsEquiv F) _ (by
    funext c
    apply Eq.symm
    apply (K.constantsEquiv F).symm_apply_eq.mpr
    change c = K.Raw.constantValue F (K.Raw.C c)
    by_cases h : c = 0 <;>
      simp [K.Raw.constantValue, K.Raw.C, K.Raw.ofPoly, MPoly.Raw.C, MPoly.Raw.constantTerm,
        Mono.trim, Poly.Raw.trim, h])

end SympyProofs.Calculus.Antiderivative
