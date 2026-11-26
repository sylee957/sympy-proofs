module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Spanning
public import SympyProofs.Calculus.Antiderivative.Proof.Row
public import SympyProofs.Calculus.Antiderivative.Program.Solve
public import SympyProofs.Calculus.Antiderivative.Proof.Coefficients

/-! The computational column operations represent linear maps over every model field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Interpret a polynomial in the newest generator coefficient by coefficient. -/
noncomputable abbrev modelPoly (p : Poly (K R n)) : Polynomial (M k n) :=
  (Poly.equiv p).map (val k)

private theorem scalar_poly (c : k) (p : Polynomial (M k n)) :
    c • p = Polynomial.C (Model.C k n c) * p := by
  rw [Algebra.smul_def]
  rfl

/-- In the model, interpret a column as its coordinates, its polynomial primitive and its
remaining polynomial right-hand side. -/
noncomputable def Column.value (width : ℕ) (c : Column R n) :
    (Fin width → k) × Polynomial (M k n) × Polynomial (M k n) :=
  (Linear.vector (Model.constantHom k) width c.params, modelPoly k c.solution,
    modelPoly k c.residual)

private theorem model_mix (cs : List (K R 0)) (ps : List (Poly (K R n))) :
    modelPoly k (mix cs ps) =
      ∑ i : Fin ps.length, Model.constantHom k (cs.getD i 0) • modelPoly k (ps.get i) := by
  induction ps generalizing cs with
  | nil => cases cs <;> simp [mix, modelPoly]
  | cons p ps ih =>
    cases cs with
    | nil => simp [mix, modelPoly]
    | cons c cs =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
        List.get_cons_zero, scalar_poly, Model.C_constantHom]
      simpa [mix, modelPoly, scalar_poly, Model.C_constantHom] using ih cs

theorem model_coordinates {F : Type} [Field F] (f : F →+* k)
    (m : ℕ) (cs : List F) (vs : List (List F)) (j : Fin m) :
    f ((coordinates m cs vs).getD j 0) =
      ∑ i : Fin vs.length, f (cs.getD i 0) * f ((vs.get i).getD j 0) := by
  simp only [coordinates, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    j.isLt, Option.map_some, Option.getD_some]
  rw [Linear.map_dot, Linear.functional_apply]
  simp [Linear.vector, List.getD_eq_getElem?_getD]
  apply Fintype.sum_equiv (finCongr (List.length_map ..))
  intro i
  have hi : i.val < vs.length := by simpa using i.isLt
  simp [List.getElem?_eq_getElem hi]

/-- Recombining a family of columns computes the usual model-linear map on coordinate vectors. -/
theorem value_combine (width : ℕ) (vs : List (Column R n)) (cs : List (K R 0)) :
    (combine width vs cs).value k width =
      Linear.accumulate vs (Column.value k width) (Linear.vector (Model.constantHom k) vs.length cs)
      := by
  rw [Linear.accumulate_apply]
  apply Prod.ext
  · ext j
    change Model.constantHom k ((coordinates width cs (vs.map Column.params)).getD j 0) = _
    rw [model_coordinates]
    simp [Column.value, Linear.vector, Prod.fst_sum, Finset.sum_apply]
    exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ (fun _ => rfl)
  · apply Prod.ext
    · change modelPoly k (mix cs (vs.map Column.solution)) = _
      rw [model_mix]
      simp [Column.value, Linear.vector, Prod.snd_sum, Prod.fst_sum]
      exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ (fun _ => rfl)
    · change modelPoly k (mix cs (vs.map Column.residual)) = _
      rw [model_mix]
      simp [Column.value, Linear.vector, Prod.snd_sum]
      exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ (fun _ => rfl)

end SympyProofs.Calculus.Antiderivative.Solve
