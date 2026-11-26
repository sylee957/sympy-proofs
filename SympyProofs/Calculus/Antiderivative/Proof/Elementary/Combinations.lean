module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Directions

/-! Linear combinations of input coordinates, answers and residual Laurent numerators. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {k F U V α β : Type} [Field k] [Field F] [AddCommGroup V] [Module k V]

namespace Linear

theorem accumulate_map (xs : List α) (f : α → β) (v : β → V) (c : Fin xs.length → k) :
    accumulate (xs.map f) v (fun i => c (Fin.cast (List.length_map ..) i)) =
      accumulate xs (fun x => v (f x)) c := by
  rw [accumulate_apply, accumulate_apply]
  exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ fun _ => by simp

theorem accumulate_vector_map (φ : F →+* k) (xs : List α) (f : α → β) (v : β → V) (q : List F) :
    accumulate (xs.map f) v (vector φ _ q) = accumulate xs (fun x => v (f x)) (vector φ _ q) :=
  accumulate_map xs f v (vector φ _ q)

theorem map_accumulate [AddCommGroup U] [Module k U] (T : U →ₗ[k] V) (xs : List α)
    (v : α → U) (c : Fin xs.length → k) :
    T (accumulate xs v c) = accumulate xs (fun x => T (v x)) c := by
  simp only [accumulate_apply, map_sum, map_smul]

theorem vector_coordinates (φ : F →+* k) (w : ℕ) (xs : List α) (f : α → List F) (cs : List F) :
    vector φ w (Solve.coordinates w cs (xs.map f)) =
      accumulate xs (fun x => vector φ w (f x)) (vector φ xs.length cs) := by
  ext j
  change φ ((Solve.coordinates w cs (xs.map f)).getD j 0) = _
  rw [Solve.model_coordinates]
  simp [accumulate_apply, vector, Finset.sum_apply]
  exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ (fun _ => rfl)

end Linear

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k) [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Scalar multiplication in the model multiplies by the corresponding constant fraction. -/
theorem Model.smul_eq_C_mul (c : k) (x : M k n) : c • x = Model.C k n c * x := by
  rw [Algebra.smul_def]
  rfl

theorem Model.accumulate_vector (cs : List k) (gs : List (K R n)) (h : cs.length = gs.length) :
    Linear.accumulate gs (val k) (Linear.vector (RingHom.id k) _ cs) =
      Model.linearCombination k cs gs := by
  have e := Solve.linearCombination_ofFn k gs id (Linear.vector (RingHom.id k) _ cs)
  have hv : List.ofFn (Linear.vector (RingHom.id k) gs.length cs) = cs := by
    apply List.ext_getElem
    · simpa using h.symm
    · intro i hi hi'
      simp [Linear.vector, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  rw [hv, List.map_id] at e
  rw [Linear.accumulate_apply]
  simpa only [smul_eq_C_mul, id_eq] using e.symm

theorem Model.accumulate_constants (cs : List (K R 0)) (gs : List (K R n))
    (h : cs.length = gs.length) :
    Linear.accumulate gs (val k) (Linear.vector (Model.constantHom k) _ cs) =
      Model.linearCombination k (cs.map (Model.constantHom k)) gs := by
  rw [← Model.accumulate_vector k _ _ (by simpa using h)]
  apply congrArg (Linear.accumulate gs (val k))
  ext i
  have hi : i.val < cs.length := h.symm ▸ i.isLt
  simp [Linear.vector, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem fold_answers (t : Tower R n) (as : List (Answer R n)) (acc : Answer R n) :
    (as.foldl Answer.add acc).deriv k t =
      acc.deriv k t + (as.map (Answer.deriv k t)).sum ∧
    ((as.foldl Answer.add acc).Regular k ↔ acc.Regular k ∧ ∀ a ∈ as, a.Regular k) := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [(ih (acc.add a)).1, (ih (acc.add a)).2, Answer.deriv_add, Answer.regular_add]
    simp [add_assoc, and_assoc]

theorem Answer.combine_regular (t : Tower R n) (cs : List (K R 0)) (as : List (Answer R n))
    (h : ∀ a ∈ as, a.Regular k) : (Answer.combine cs as).Regular k := by
  rw [Answer.combine, (fold_answers k t _ _).2]
  refine ⟨by simp [Answer.Regular], ?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  rw [List.getElem_zipWith, Answer.regular_scale]
  exact h _ (List.getElem_mem _)

theorem Answer.combine_deriv (t : Tower R n) (cs : List (K R 0)) (as : List (Answer R n)) :
    (Answer.combine cs as).deriv k t =
      Linear.accumulate as (Answer.deriv k t)
        (Linear.vector (Model.constantHom k) as.length cs) := by
  rw [Answer.combine, (fold_answers k t _ _).1, Linear.accumulate_apply]
  rw [show (⟨0,[]⟩ : Answer R n).deriv k t = 0 by simp [Answer.deriv], zero_add]
  induction as generalizing cs with
  | nil => cases cs <;> simp
  | cons a as ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    cases cs with
    | nil => simp [Linear.vector]
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons, Answer.deriv_scale,
        Linear.vector, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
        List.get_cons_zero, Model.smul_eq_C_mul, Model.C_constantHom]
      congr 1
      simpa [Linear.vector, Model.smul_eq_C_mul, Model.C_constantHom] using ih cs

end SympyProofs.Calculus.Antiderivative
