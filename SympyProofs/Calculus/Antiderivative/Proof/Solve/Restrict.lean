module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Columns

/-! Vanishing of the high-degree residual is exactly the column-space restriction applied by
the polynomial differential solver. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Finite-coordinate specialization of the model's linear combination. -/
theorem linearCombination_ofFn {α : Type} (xs : List α) (v : α → K R n)
    (a : Fin xs.length → k) :
    Model.linearCombination k (List.ofFn a) (xs.map v) =
      ∑ i : Fin xs.length, Model.C k n (a i) * val k (v (xs.get i)) := by
  induction xs with
  | nil => simp [Model.linearCombination]
  | cons x xs ih =>
    simp only [List.length_cons] at a
    rw [List.ofFn_succ, List.map_cons]
    change _ + Model.linearCombination k _ _ = _
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ, ih]
    rfl

theorem functional_ofFn {m : ℕ} (a : Fin m → k) (r : List (K R 0)) :
    Model.rowHolds k r (List.ofFn a) ↔ Linear.functional (Model.constantHom k) m r a = 0 := by
  rw [Model.rowHolds_iff_functional]
  simp only [Linear.functional_apply, Linear.vector, RingHom.id_apply]
  apply Iff.of_eq
  apply congrArg (· = 0)
  apply Fintype.sum_equiv (finCongr List.length_ofFn)
  intro i
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]
  exact Or.inl rfl

theorem residual_coeff (w : ℕ) (vs : List (Column R n)) (a : Fin vs.length → k) (j : ℕ) :
    (Linear.accumulate vs (Column.value k w) a).2.2.coeff j =
      Model.linearCombination k (List.ofFn a) (vs.map fun c => c.residual.coeff j) := by
  rw [linearCombination_ofFn]
  rw [Linear.accumulate_apply, Prod.snd_sum, Prod.snd_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  change (a i • modelPoly k (vs.get i).residual).coeff j = _
  rw [AddMonoidAlgebra.coeff_smul_apply, Algebra.smul_def, modelPoly, Polynomial.coeff_map,
    Poly.coeff_equiv]
  rfl

private theorem mem_drop_slices (ps : List (Poly (K R n))) (lo : ℕ) (row : List (K R n)) :
    row ∈ (coefficientSlices ps).drop lo ↔
      ∃ j, lo ≤ j ∧ j < (ps.map (·.coeffs.length)).max?.getD 0 ∧ row = ps.map (·.coeff j) := by
  let N := (ps.map (·.coeffs.length)).max?.getD 0
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i,hi,rfl⟩
    have hi' : i < N - lo := by simpa [coefficientSlices, N] using hi
    exact ⟨lo+i, by omega, by omega, by simp [List.getElem_drop, coefficientSlices]⟩
  · rintro ⟨j,hlo,hj,rfl⟩
    have hj' : j < N := hj
    refine ⟨j-lo, by simpa [coefficientSlices, ← show (ps.map (·.coeffs.length)).max?.getD 0 = N
      from rfl] using (show j-lo < N-lo by omega), ?_⟩
    simp [List.getElem_drop, coefficientSlices, show lo+(j-lo) = j by omega]

private theorem restrict_equations (w lo : ℕ) (vs : List (Column R n)) (a : Fin vs.length → k) :
    (∀ r ∈ ((coefficientSlices (vs.map Column.residual)).drop lo).flatMap rowsOf,
      Linear.functional (Model.constantHom k) vs.length r a = 0) ↔
        ∀ j ≥ lo, (Linear.accumulate vs (Column.value k w) a).2.2.coeff j = 0 := by
  let ps := vs.map Column.residual
  let N := (ps.map (·.coeffs.length)).max?.getD 0
  simp_rw [← functional_ofFn, residual_coeff k]
  change (∀ r ∈ ((coefficientSlices ps).drop lo).flatMap rowsOf, _) ↔ _
  constructor
  · intro h j hj
    by_cases hN : j < N
    · have hm := (mem_drop_slices ps lo _).mpr ⟨j,hj,hN,rfl⟩
      have hh := (rowsOf_spec k (ps.map (·.coeff j)) (List.ofFn a)).mp
        (fun r hr => h r (List.mem_flatMap.mpr ⟨_,hm,hr⟩))
      simpa [ps, List.map_map, Function.comp_def] using hh
    · rw [linearCombination_ofFn]
      apply Finset.sum_eq_zero
      intro i _
      have hmem : (vs.get i).residual ∈ ps := List.mem_map_of_mem (vs.get_mem i)
      have hlen : (vs.get i).residual.coeffs.length ≤ j :=
        (List.le_max?_getD_of_mem (List.mem_map_of_mem (f := fun p : Poly (K R n) =>
          p.coeffs.length) hmem)).trans (Nat.le_of_not_lt hN)
      have hzero : (vs.get i).residual.coeff j = 0 := by
        rw [Poly.coeff_eq_getD_coeffs]
        exact Poly.Raw.coeff_eq_zero_of_length_le hlen
      change _ * val k ((vs.get i).residual.coeff j) = 0
      rw [hzero, map_zero, mul_zero]
  · rintro h r hr
    obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨j,hj,_,rfl⟩ := (mem_drop_slices ps lo s).mp hs
    apply (rowsOf_spec k _ _).mpr _ r hr
    simpa [ps, List.map_map, Function.comp_def] using h j hj

/-- The restricted columns span precisely the old combinations whose residual has all
coefficients from the cutoff onwards equal to zero. -/
theorem mem_restrict_iff (w lo : ℕ) (vs : List (Column R n))
    (y : (Fin w → k) × Polynomial (M k n) × Polynomial (M k n)) :
    y ∈ Submodule.span k (Column.value k w '' {c | c ∈ restrict w lo vs}) ↔
      y ∈ Submodule.span k (Column.value k w '' {c | c ∈ vs}) ∧ ∀ j ≥ lo, y.2.2.coeff j = 0 := by
  rw [restrict, Linear.mem_columns_iff vs (Column.value k w) y]
  split
  · rename_i he
    rw [Linear.mem_columns_iff]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a,rfl⟩, (restrict_equations k w lo vs a).mp (by rw [List.isEmpty_iff.mp he]; simp)⟩
    · exact And.left
  · rw [Linear.mem_kernel_image_iff (Model.constantHom k) _ _
      (Linear.accumulate vs (Column.value k w))
      _ _ (fun q _ => value_combine k w vs q)]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,rfl⟩, (restrict_equations k w lo vs a).mp ha⟩
    · rintro ⟨⟨a,rfl⟩,h⟩
      exact ⟨a,(restrict_equations k w lo vs a).mpr h,rfl⟩

end SympyProofs.Calculus.Antiderivative.Solve
