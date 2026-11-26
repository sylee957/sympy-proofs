module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Interpolation
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Split
public import SympyProofs.Calculus.Antiderivative.Spec.Factor
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Gauss

/-! Gauss's lemma and interpolation give the complete rational polynomial factorization. -/

public section

namespace SympyProofs.Calculus.Antiderivative

namespace Factor

private theorem integral_associated (p : Poly ℚ) :
    Associated ((Poly.equiv (integral p)).map (Int.castRingHom ℚ)) (Poly.equiv p) := by
  rw [integral_eq, mul_comm]
  exact associated_mul_unit_left _ _ (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (by exact_mod_cast (denominator_pos p.coeffs).ne')))

/-- A reducible rational polynomial has an integral divisor whose positive degree is at
most half its degree and whose values divide all values of its integral multiple. -/
theorem integral_divisor {p : Poly ℚ} (hd : 2 ≤ p.natDegree) (hI : ¬Irreducible p) :
    ∃ b : Polynomial ℤ, b ∣ Poly.equiv (integral p) ∧
      0 < b.natDegree ∧ b.natDegree ≤ p.natDegree / 2 ∧
      b.map (Int.castRingHom ℚ) ∣ Poly.equiv p := by
  have hp : Poly.equiv p ≠ 0 := fun e => by
    have := congrArg Polynomial.natDegree e
    simp at this
    omega
  have hnp := (Poly.equiv p).not_isUnit_of_natDegree_pos
    (by simpa using (show 0 < p.natDegree by omega))
  have hI' : ¬ Irreducible (Poly.equiv p) := fun h =>
    hI ((MulEquiv.irreducible_iff (Poly.equiv (R := ℚ))).mp h)
  rw [Polynomial.irreducible_iff_lt_natDegree_lt hp hnp] at hI'
  push Not at hI'
  obtain ⟨b, _, hb, hdiv⟩ := hI'
  rw [Finset.mem_Ioc, Poly.natDegree_equiv] at hb
  have b0 : b ≠ 0 := fun e => by simp [e] at hb
  have dvdint := (integral_associated p).dvd_iff_dvd_right.mpr hdiv
  obtain ⟨g, hgp, hg, he⟩ := lift_fraction_divisor (Poly.equiv (integral p)) b b0 dvdint
  exact ⟨g, hgp, he.symm ▸ hb.1, he.symm ▸ hb.2, hg.dvd_iff_dvd_left.mpr hdiv⟩

private theorem eval_map_int (z : Polynomial ℤ) (i : ℕ) :
    (z.map (Int.castRingHom ℚ)).eval (i : ℚ) = (Int.castRingHom ℚ) (z.eval (i : ℤ)) := by
  rw [Polynomial.eval_map]
  simp

private theorem root_proper {p : Poly ℚ} (hd : 2 ≤ p.natDegree) {i : ℕ}
    (hi : (integral p).eval (i : ℤ) = 0) : proper p (Poly.X - Poly.C (i : ℚ)) := by
  have e := congrArg (Polynomial.eval (i : ℚ)) (integral_eq p).symm
  rw [eval_map_int, Poly.eval_equiv, hi, map_zero, Polynomial.eval_mul, Polynomial.eval_C] at e
  have hdn : (denominator p.coeffs : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos _).ne'
  have hroot := (mul_eq_zero.mp e).resolve_left hdn
  have hdeg : (Poly.X - Poly.C (i : ℚ)).natDegree = 1 := by
    rw [← Poly.natDegree_equiv, map_sub, Poly.equiv_X, Poly.equiv_C, Polynomial.natDegree_X_sub_C]
  apply (proper_iff _ _).mpr
  refine ⟨by omega, by omega, ?_⟩
  have dvd := Polynomial.dvd_iff_isRoot.mpr hroot
  simpa only [map_sub, Poly.equiv_symm_X, Poly.equiv_symm_C, RingEquiv.symm_apply_apply]
    using (map_dvd (Poly.equiv (R := ℚ)).symm dvd)

/-- Every factor reported by the integer divisor search divides the input properly. -/
theorem rationalDivisor_proper {p q : Poly ℚ} (hd : 2 ≤ p.natDegree)
    (h : rationalDivisor p = some q) : proper p q := by
  obtain ⟨i, _, hi⟩ := List.exists_of_findSome?_eq_some h
  rw [tryDegree] at hi
  split at hi
  · rename_i j hj
    cases hi
    apply root_proper hd
    have yes := List.find?_some hj
    exact eq_of_beq yes
  · exact interpolateFactor_proper hi

/-- A reducible input always produces a divisor. -/
theorem rationalDivisor_complete (p : Poly ℚ) (hd : 2 ≤ p.natDegree) (hI : ¬Irreducible p) :
    ∃ q, rationalDivisor p = some q ∧ proper p q := by
  obtain ⟨b, hb, hb0, hdeg, hbp⟩ := integral_divisor hd hI
  let q : Poly ℚ := Poly.equiv.symm (b.map (Int.castRingHom ℚ))
  have eqv : Poly.equiv q = b.map (Int.castRingHom ℚ) := Poly.equiv.apply_symm_apply _
  have qdeg : q.natDegree = b.natDegree := by
    rw [← Poly.natDegree_equiv, eqv]
    exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective b
  have qp : proper p q := (proper_iff _ _).mpr ⟨by omega, by omega,
    by simpa [q] using map_dvd (Poly.equiv (R := ℚ)).symm hbp⟩
  have search : (rationalDivisor p).isSome := by
    apply List.findSome?_isSome_iff.mpr
    refine ⟨b.natDegree - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [show b.natDegree - 1 + 1 = b.natDegree by omega, tryDegree]
    split
    · rfl
    rename_i hNone
    apply interpolateFactor_isSome _ _ _ (fun i => b.eval (i : ℤ))
    · intro i hi
      apply mem_signedDivisors
      · simpa using List.find?_eq_none.mp hNone i hi
      · simpa using map_dvd (Polynomial.evalRingHom (i : ℤ)) hb
    · simp only [zero_add]
      have ev (i : ℕ) : (Int.castRingHom ℚ) (b.eval (i : ℤ)) = q.eval (i : ℚ) := by
        rw [← Poly.eval_equiv, eqv, eval_map_int]
      change proper p (((List.range (b.natDegree + 1)).map fun (i : ℕ) =>
        Poly.C ((Int.castRingHom ℚ) (b.eval (i : ℤ))) * basis b.natDegree i).sum)
      simpa only [ev, reconstruct q qdeg.le] using qp
  cases he : rationalDivisor p with
  | none => simp [he] at search
  | some q => exact ⟨q, rfl, rationalDivisor_proper hd he⟩

end Factor

/-- The rational factorization produces precisely monic irreducibles with the stated product. -/
instance : LawfulConstantFactors ℚ where
  irreducible p _ q h :=
    ⟨Factor.split_monic _ _ _ h, Factor.split_irreducible _ Factor.rationalDivisor_complete
      _ _ (le_refl _) h⟩
  product p hp := by
    change Poly.C p.leadingCoeff * (Factor.split _ _ p).prod = p
    rw [Factor.split_prod _ _ _ hp, Poly.normalize_eq_C_mul, ← mul_assoc, ← Poly.C_mul,
      mul_inv_cancel₀ (Poly.leadingCoeff_ne_zero hp), Poly.C_one, one_mul]

end SympyProofs.Calculus.Antiderivative
