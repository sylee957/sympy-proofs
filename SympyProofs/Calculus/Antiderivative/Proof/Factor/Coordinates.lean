module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Model
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Sparse

/-! Coordinate compatibility of the sparse evaluator with parameter polynomials. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

private theorem descend_comp {F G : Type} [Field F] [Field G] {n : ℕ} (f : F →+* G)
    (g : K R n →+* F) : descend (f.comp g) = f.comp (descend g) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (g.comp K.lift)

private theorem polyMap_C {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]
    (f : F →+* G) (a : F) : (Poly.C a).map f = Poly.C (f a) :=
  Poly.equiv.injective (by rw [Poly.equiv_map, Poly.equiv_C, Polynomial.map_C, Poly.equiv_C])

private theorem parameters_map {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]
    {n : ℕ} (f : F →+* G) (g : K R n →+* F) (vs : List (Poly F)) :
    parameters (f.comp g) (vs.map (Poly.map f)) = (parameters g vs).map (Poly.map f) := by
  induction n generalizing vs with
  | zero => rfl
  | succ n ih =>
    rw [parameters, parameters]
    convert ih (g.comp K.lift) (Poly.C (g K.gen) :: vs) using 1
    simp [polyMap_C]
    rfl

private theorem parameters_append {F : Type} [Field F] [DecidableEq F] {n : ℕ}
    (g : K R n →+* F) (vs ws : List (Poly F)) :
    parameters g (vs ++ ws) = parameters g vs ++ ws := by
  induction n generalizing vs with
  | zero => rfl
  | succ n ih => exact ih (g.comp K.lift) (Poly.C (g K.gen) :: vs)

/-- Include the coefficient constants in the rational function model. -/
private noncomputable def ground (n : ℕ) : K R 0 →+* M (K R 0) n :=
  (algebraMap (MvPolynomial (Fin n) (K R 0)) _).comp MvPolynomial.C

/-- The model rational function represented by one coordinate. -/
private noncomputable def param (n : ℕ) (i : Fin n) : M (K R 0) n :=
  algebraMap (MvPolynomial (Fin n) (K R 0)) _ (MvPolynomial.X i)

private theorem overConstants_comp_lift (n : ℕ) :
    (overConstants (R := R) (n+1)).toRingHom.comp K.lift =
      (Model.includeVars (Nat.le_succ n)).comp (overConstants n).toRingHom :=
  RingHom.ext (overConstants_lift ·)

private theorem descend_constants (n : ℕ) :
    descend (overConstants (R := R) n).toRingHom = ground n := by
  induction n with
  | zero =>
    ext c
    apply (K.modelConstantsEquiv (R := K R 0) (K R 0)).injective
    change (K.modelConstantsEquiv (K R 0)) ((K.modelConstantsEquiv (K R 0)).symm c) = _
    rw [RingEquiv.apply_symm_apply]
    rw [ground, RingHom.comp_apply, K.modelConstantsEquiv,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, ← MvPolynomial.isEmptyRingEquiv_symm_apply,
      RingEquiv.apply_symm_apply]
    rfl
  | succ n ih =>
    rw [descend, overConstants_comp_lift, descend_comp, ih]
    ext c
    simp [ground, Model.includeVars_polynomial]

private theorem parameters_constants (n : ℕ) :
    parameters (overConstants (R := R) n).toRingHom [] =
      List.ofFn fun i : Fin n => Poly.C (param n i) := by
  induction n with
  | zero => simp [parameters]
  | succ n ih =>
    rw [parameters, overConstants_comp_lift, List.ofFn_succ']
    have post := parameters_append
      ((Model.includeVars (Nat.le_succ n)).comp (overConstants (R := R) n).toRingHom)
      [] [Poly.C ((overConstants (R := R) (n + 1)).toRingHom K.gen)]
    rw [List.nil_append] at post
    rw [post]
    have main := parameters_map (Model.includeVars (R := K R 0) (Nat.le_succ n))
      (overConstants (R := R) n).toRingHom []
    rw [List.map_nil, ih, List.map_ofFn] at main
    rw [main, List.concat_eq_append]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [polyMap_C, param, Model.includeVars_polynomial]
    all_goals first | rfl | exact congrArg (fun z => [Poly.C z]) overConstants_gen

/-- The model polynomial evaluates the lower variables in the rational function field and
retains its last variable as a polynomial indeterminate. -/
noncomputable def parameterHom (n : ℕ) :
    MvPolynomial (Fin (n+1)) (K R 0) →+* Polynomial (M (K R 0) n) :=
  (Polynomial.mapRingHom (algebraMap _ _)).comp (Model.splitPolynomial (K R 0) n).toRingHom

private theorem map_monomialValue {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]
    (e : F ≃+* G) (vs : List (Poly F)) (m : List ℕ) :
    Poly.interpret e (monomialValue vs m) =
      Poly.equiv (monomialValue (vs.map (Poly.map e)) m) := by
  induction vs generalizing m with
  | nil => cases m <;> simp [monomialValue]
  | cons v vs ih =>
    cases m with
    | nil => simp [monomialValue]
    | cons a m =>
      rw [monomialValue, map_mul, map_pow, ih]
      simp only [List.map_cons, monomialValue, map_mul, map_pow]
      congr 2
      exact (Poly.equiv_map e.toRingHom v).symm

private theorem interpret_restore {F G H : Type} [Field F] [Field G] [Field H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+* H) (f : F →+* G) (vs : List (Poly G))
    {k : ℕ} (P : MvPolynomial (Fin k) F) :
    Poly.interpret e (restoreHom f vs k P) =
      Poly.equiv (restoreHom (e.toRingHom.comp f) (vs.map (Poly.map e)) k P) := by
  conv_lhs => rw [P.as_sum, map_sum, map_sum]
  conv_rhs => rw [P.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [restoreHom_monomial, restoreHom_monomial, map_mul, map_mul, map_monomialValue]
  simp [Poly.interpret_apply]

private theorem restore_parameters (n : ℕ) :
    Poly.equiv.toRingHom.comp (restoreHom (ground (R := R) n)
      ((List.ofFn fun i : Fin n => Poly.C (param n i)) ++ [Poly.X]) (n+1)) = parameterHom n := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change Poly.equiv (restoreHom _ _ _ (MvPolynomial.C c)) =
      ((Model.splitPolynomial (K R 0) n) (MvPolynomial.C c)).map _
    have hc : Model.splitPolynomial (K R 0) n (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := by
      exact (Model.splitPolynomial (K R 0) n).commutes c
    rw [restoreHom, MvPolynomial.eval₂Hom_C, hc, Polynomial.map_C]
    exact Poly.equiv_C _
  · intro i
    change Poly.equiv (restoreHom _ _ _ (MvPolynomial.X i)) =
      ((Model.splitPolynomial (K R 0) n) (MvPolynomial.X i)).map _
    rw [restoreHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    induction i using Fin.lastCases with
    | last =>
      simp [List.getD_eq_getElem?_getD, Model.splitPolynomial_last]
    | cast i =>
      simp [List.getD_eq_getElem?_getD, i.isLt,
        param, Model.splitPolynomial_castSucc]

/-- Restoring the sparse variables agrees with splitting the last variable and interpreting
the coefficient polynomials over the constant field. -/
theorem restore_parameterHom (n : ℕ) (P : MvPolynomial (Fin (n+1)) (K R 0)) :
    let f := RingHom.id (K R n)
    Poly.interpret (overConstants n) (restoreHom (descend f) (parameters f [Poly.X]) (n+1) P) =
      parameterHom n P := by
  dsimp only
  let e := (overConstants (R := R) n).toRingHom
  have hd : e.comp (descend (RingHom.id (K R n))) = ground n := by
    rw [← descend_comp, RingHom.comp_id]
    exact descend_constants n
  have hv : (parameters (RingHom.id (K R n)) [Poly.X]).map (Poly.map e) =
      (List.ofFn fun i : Fin n => Poly.C (param n i)) ++ [Poly.X] := by
    rw [← parameters_map, RingHom.comp_id]
    have hx : (Poly.X : Poly (K R n)).map e = Poly.X :=
      Poly.equiv.injective (by rw [Poly.equiv_map, Poly.equiv_X, Polynomial.map_X, Poly.equiv_X])
    rw [List.map_cons, List.map_nil, hx]
    exact (parameters_append e [] [Poly.X]).trans
      (congrArg (· ++ [Poly.X]) (parameters_constants n))
  rw [interpret_restore, hd]
  change Poly.equiv (restoreHom (ground n)
    ((parameters (RingHom.id (K R n)) [Poly.X]).map (Poly.map e)) _ P) = _
  rw [hv]
  exact DFunLike.congr_fun (restore_parameters n) P

end SympyProofs.Calculus.Antiderivative.Factor
