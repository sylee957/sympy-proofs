module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Restrict
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Coefficients

/-! One lower-field differential solve, including all possible leading coefficients of a
partial polynomial solution. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

private theorem scalar_field (c : k) (x : M k n) : c • x = Model.C k n c * x := by
  rw [Algebra.smul_def]
  rfl

private theorem accumulate_field (hs : List (K R n)) (a : Fin hs.length → k) :
    Linear.accumulate hs (val k) a = Model.linearCombination k (List.ofFn a) hs := by
  have h := linearCombination_ofFn k hs id a
  rw [Linear.accumulate_apply]
  simpa only [List.map_id, scalar_field, id_eq] using h.symm

private theorem combine_as_sum (ds : List (K R 0)) (hs : List (K R n)) :
    val k (Level.combine ds hs) = Linear.accumulate hs (val k)
      (Linear.vector (Model.constantHom k) hs.length ds) := by
  rw [Linear.accumulate_apply]
  induction hs generalizing ds with
  | nil => cases ds <;> simp [Level.combine]
  | cons h hs ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    cases ds with
    | nil => simp [Level.combine, Linear.vector]
    | cons c ds =>
      simp only [Level.combine, List.zipWith_cons_cons, List.sum_cons, map_add, map_mul,
        Linear.vector, Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ,
        List.get_cons_zero, scalar_field, Model.C_constantHom]
      congr 1
      simpa [Linear.vector, scalar_field, Model.C_constantHom, Level.combine] using ih ds

/-- The linear map that keeps the input coefficients and forms a solution as a combination of
the lower solver's returned field elements. -/
noncomputable def parameterMap (m : ℕ) (hs : List (K R n)) :
    (Fin (m+hs.length) → k) →ₗ[k] (Fin m → k) × M k n :=
  (LinearMap.pi fun i => LinearMap.proj (Fin.castAdd hs.length i)).prod
    ((Linear.accumulate hs (val k)).comp (LinearMap.pi fun i => LinearMap.proj (Fin.natAdd m i)))

private theorem parameterMap_vector (m : ℕ) (hs : List (K R n)) (q : List (K R 0)) :
    (Linear.vector (Model.constantHom k) m q, val k (Level.combine (q.drop m) hs)) =
      parameterMap k m hs (Linear.vector (Model.constantHom k) _ q) := by
  refine Prod.ext rfl ?_
  rw [combine_as_sum]
  apply congrArg (Linear.accumulate hs (val k))
  ext i
  simp [Linear.vector, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The joint kernel of the parameter and solution constraints spans exactly the graph
described by the field generators and homogeneous rows. -/
theorem parameterGraph_iff (m : ℕ) (hs : List (K R n)) (rows : List (List (K R 0)))
    (a : Fin m → k) (y : M k n) :
    (a,y) ∈ Submodule.span k
        ((fun q : List (K R 0) => (Linear.vector (Model.constantHom k) m q,
          val k (Level.combine (q.drop m) hs))) ''
          {q | q ∈ Linear.kernel rows (m + hs.length)}) ↔
      ∃ ds : List k, ds.length = hs.length ∧ y = Model.linearCombination k ds hs ∧
        ∀ row ∈ rows, Model.rowHolds k row (List.ofFn a ++ ds) := by
  let coordinates := fun q : List (K R 0) =>
    (Linear.vector (Model.constantHom k) m q, val k (Level.combine (q.drop m) hs))
  have him := Linear.mem_kernel_image_iff (Model.constantHom k) rows (m+hs.length)
    (parameterMap k m hs) id coordinates (fun q _ => parameterMap_vector k m hs q) (a,y)
  simp only [List.map_id] at him
  change (a,y) ∈ Submodule.span k (coordinates '' {q | q ∈ Linear.kernel rows (m+hs.length)}) ↔ _
  rw [him]
  constructor
  · rintro ⟨v,hv,eqn⟩
    let d : Fin hs.length → k := fun i => v (Fin.natAdd m i)
    have ha (i : Fin m) : v (Fin.castAdd _ i) = a i := congrFun (congrArg Prod.fst eqn) i
    have hv' : Fin.append a d = v := by
      ext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · exact (Fin.append_left ..).trans (ha i).symm
      · exact Fin.append_right ..
    refine ⟨List.ofFn d, List.length_ofFn, ?_, ?_⟩
    · rw [← accumulate_field]
      exact (congrArg Prod.snd eqn).symm
    · intro r hr
      rw [← List.ofFn_fin_append, functional_ofFn, hv']
      exact hv r hr
  · rintro ⟨ds,hd,hy,hr⟩
    let d (i : Fin hs.length) := ds.get ⟨i, hd.symm ▸ i.isLt⟩
    have hd' : List.ofFn d = ds := by
      apply List.ext_getElem
      · simpa using hd.symm
      · intro i hi hj
        simp [d]
    refine ⟨Fin.append a d, ?_, Prod.ext ?_ ?_⟩
    · intro r hm
      rw [← functional_ofFn, List.ofFn_fin_append, hd']
      exact hr r hm
    · ext i
      exact Fin.append_left ..
    · change Linear.accumulate hs (val k) (fun i => Fin.append a d (Fin.natAdd m i)) = y
      have eqv : (fun i => Fin.append a d (Fin.natAdd m i)) = d :=
        funext fun _ => Fin.append_right ..
      rw [eqv, accumulate_field, hd']
      exact hy.symm

/-- The computed homogeneous kernel, after combining the lower solution coefficients, spans
all pairs of input parameters and lower-field solutions of the leading coefficient equation. -/
theorem parameter_kernel_spec {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (f : K R n) (gs : List (K R n)) (a : Fin gs.length → k) (y : M k n) :
    let (hs, rows) := lower.solve f gs
    (a,y) ∈ Submodule.span k
        ((fun q : List (K R 0) => (Linear.vector (Model.constantHom k) gs.length q,
          val k (Level.combine (q.drop gs.length) hs))) ''
          {q | q ∈ Linear.kernel rows (gs.length + hs.length)}) ↔
      t.modelD k y + val k f * y = Model.linearCombination k (List.ofFn a) gs := by
  obtain ⟨hs, rows, h⟩ : ∃ hs rows, lower.solve f gs = (hs,rows) := ⟨_,_,rfl⟩
  have eqn := hl f gs y (List.ofFn a) (by simp)
  rw [h] at eqn ⊢
  exact (parameterGraph_iff k gs.length hs rows a y).trans eqn.symm

end SympyProofs.Calculus.Antiderivative.Solve
