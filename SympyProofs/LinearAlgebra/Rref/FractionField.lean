module

public import SympyProofs.LinearAlgebra.Rref.Basic
public import SympyProofs.LinearAlgebra.Rref.Normalized

/-! Scalar extension and normalization of RREF certificates.
Normalization uses an algebra map from the coefficient ring into a field.
Its validity and uniqueness over the fraction field use the additional
integral-domain hypotheses. -/

@[expose] public section

namespace SympyProofs.Rref

variable {R : Type*} [CommRing R] {m n : ℕ}

section ScalarExtension

variable {F : Type*} [Field F] [Algebra R F] [IsDomain R] [IsFractionRing R F]

/-- Clear all coordinates of a finite vector at once. This is used only in the
proof of scalar extension, not stored in the fraction-free RREF result. -/
theorem exists_integral_multiple {n : ℕ} (x : Fin n → F) :
    ∃ (d : R) (y : Fin n → R), d ≠ 0 ∧
      (algebraMap R F ∘ y) = algebraMap R F d • x := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) x
  choose y hy using hd
  refine ⟨d, y, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  funext j
  simpa [Algebra.smul_def] using hy j

/-- Rectangular matrices with the same kernel over the domain have the same
kernel after passage to a fraction field. Their row counts may differ. -/
theorem kernel_iff_fractionField {m l n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin l) (Fin n) R)
    (h : ∀ y, A.mulVec y = 0 ↔ B.mulVec y = 0) (x : Fin n → F) :
    (A.map (algebraMap R F)).mulVec x = 0 ↔
      (B.map (algebraMap R F)).mulVec x = 0 := by
  obtain ⟨d, y, hd, hy⟩ := exists_integral_multiple (R := R) x
  have hdF : algebraMap R F d ≠ 0 :=
    fun hz => hd ((IsFractionRing.to_map_eq_zero_iff).mp hz)
  have hm {k : ℕ} (M : Matrix (Fin k) (Fin n) R) :
      M.mulVec y = 0 ↔ (M.map (algebraMap R F)).mulVec x = 0 := by
    have he : algebraMap R F ∘ M.mulVec y =
        algebraMap R F d • (M.map (algebraMap R F)).mulVec x := by
      ext i
      rw [Function.comp_apply, RingHom.map_mulVec]
      rw [hy, Matrix.mulVec_smul]
    constructor
    · intro hz
      rw [hz] at he
      have hz' : algebraMap R F d • (M.map (algebraMap R F)).mulVec x = 0 := by
        simpa using he.symm
      exact (smul_eq_zero.mp hz').resolve_left hdF
    · intro hz
      rw [hz, smul_zero] at he
      ext i
      exact (IsFractionRing.to_map_eq_zero_iff).mp (congrFun he i)
  rw [← hm A, ← hm B, h]

end ScalarExtension

section Normalization

variable (F : Type*) [Field F] [Algebra R F]

/-- Interpret the scale already present in the pivot entry. -/
def RrefResult.normalizedRow (r : RrefResult R m n) (p j : Fin n) : F :=
  algebraMap R F (r.row p j) / algebraMap R F (r.row p p)

/-- Ordered, normalized mathematical view; extraction need not construct it. -/
def RrefResult.normalized (r : RrefResult R m n) : NormalizedRref F m n where
  matrix := fun i j => (r.sortedPivots[i.val]?).elim 0 (fun p => r.normalizedRow F p j)
  pivots := r.sortedPivots
  length_le := r.sortedPivots_length_le

/-- Read any normalized stored row at its position in the canonical view. -/
theorem RrefResult.normalized_apply (r : RrefResult R m n)
    (i : Fin m) (p j : Fin n) (hp : r.sortedPivots[i.val]? = some p) :
    (r.normalized F).matrix i j = r.normalizedRow F p j := by simp [normalized, hp]

theorem RrefResult.mapped_kernel_iff_rows {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) (x : Fin n → F) :
    (r.matrix.map (algebraMap R F)).mulVec x = 0 ↔
      ∀ p ∈ r.pivots, ∑ j, algebraMap R F (r.row p j) * x j = 0 := by
  constructor
  · intro hx p hp
    obtain ⟨v, hv⟩ := (r.mem_pivots_iff p).mp hp
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hv
    have h := congrFun hx ⟨i, hi⟩
    simpa [Matrix.mulVec, dotProduct, matrix, he, r.row_of_mem hr p v hv] using h
  · intro hx
    ext i
    let p := r.rows[i.val].1
    let v := r.rows[i.val].2
    have hv : (p, v) ∈ r.rows := by
      exact Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
    have h := hx p ((r.mem_pivots_iff p).mpr ⟨v, hv⟩)
    simpa [Matrix.mulVec, dotProduct, matrix, r.row_of_mem hr p v hv, v] using h

section FractionField

variable [IsDomain R] [IsFractionRing R F]

/-- The ring-only certificate implies a genuine normalized RREF certificate over
the fraction field. Scalar extension is proved by clearing a finite vector. -/
theorem RrefResult.normalized_valid {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m n) (hr : r.Valid A) :
    (r.normalized F).Valid (A.map (algebraMap R F)) := by
  have hordered : r.sortedPivots.Pairwise (· < ·) := r.pivots.sortedLT_sort.pairwise
  have hne (p : Fin n) (hp : p ∈ r.pivots) : algebraMap R F (r.row p p) ≠ 0 :=
    fun h => r.pivot_ne_zero hr p hp (IsFractionRing.to_map_eq_zero_iff.mp h)
  refine ⟨hordered, ?_, ?_, ?_, ?_⟩
  · intro i p hp k
    change r.sortedPivots[i.val]? = some p at hp
    have hpm : p ∈ r.pivots := (r.mem_sortedPivots p).mp (List.mem_of_getElem? hp)
    change (r.sortedPivots[k.val]?).elim 0 (fun q => r.normalizedRow F q p) = _
    by_cases hki : k = i
    · subst k
      simp [hp, normalizedRow, hne p hpm]
    · cases hq : r.sortedPivots[k.val]? with
      | none => simp [hki]
      | some q =>
        have hqm : q ∈ r.pivots := (r.mem_sortedPivots q).mp (List.mem_of_getElem? hq)
        have hpq : p ≠ q := by
          intro hpq
          apply hki
          apply Fin.ext
          apply hordered.nodup.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp hq).1
          exact hq.trans (by simpa [hpq] using hp.symm)
        simp [normalizedRow, r.row_other_pivot hr q hqm p hpm hpq, hki]
  · intro i p hp j hj
    change r.sortedPivots[i.val]? = some p at hp
    have hpm := (r.mem_sortedPivots p).mp (List.mem_of_getElem? hp)
    simp [normalized, hp, normalizedRow, r.row_before_pivot hr p hpm j hj]
  · intro i hp
    change r.sortedPivots[i.val]? = none at hp
    funext j
    simp [normalized, hp]
  · intro x
    rw [kernel_iff_fractionField A r.matrix hr.kernel_iff x,
      r.mapped_kernel_iff_rows F hr x]
    constructor
    · intro hx
      ext i
      cases hp : r.sortedPivots[i.val]? with
      | none => simp [normalized, Matrix.mulVec, dotProduct, hp]
      | some p =>
        have hpm := (r.mem_sortedPivots p).mp (List.mem_of_getElem? hp)
        simp only [normalized, Matrix.mulVec, dotProduct, hp, Option.elim_some,
          normalizedRow, div_mul_eq_mul_div, ← Finset.sum_div]
        rw [hx p hpm, zero_div]
        rfl
    · intro hx p hp
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((r.mem_sortedPivots p).mpr hp)
      let row : Fin m := ⟨i, lt_of_lt_of_le hi r.sortedPivots_length_le⟩
      have hpi : r.sortedPivots[row.val]? = some p := by simp [row, hi, he]
      have h := congrFun hx row
      simp only [normalized, Matrix.mulVec, dotProduct, hpi, Option.elim_some,
        normalizedRow, div_mul_eq_mul_div, ← Finset.sum_div, Pi.zero_apply] at h
      exact (div_eq_zero_iff.mp h).resolve_right (hne p hp)


end FractionField

end Normalization

section Domain

variable [IsDomain R]

theorem RrefResult.pivots_eq {A : Matrix (Fin m) (Fin n) R}
    (r s : RrefResult R m n) (hr : r.Valid A) (hs : s.Valid A) : r.pivots = s.pivots := by
  have h := (r.normalized (FractionRing R)).pivots_eq (s.normalized (FractionRing R))
    (r.normalized_valid (FractionRing R) hr) (s.normalized_valid (FractionRing R) hs)
  change r.sortedPivots = s.sortedPivots at h
  ext p
  rw [← r.mem_sortedPivots, h, s.mem_sortedPivots]

section FractionField

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Canonical rows are independent of storage order and all nonzero row scales. -/
theorem RrefResult.normalizedRow_eq {A : Matrix (Fin m) (Fin n) R}
    (r s : RrefResult R m n) (hr : r.Valid A) (hs : s.Valid A) :
    r.normalizedRow F = s.normalizedRow F := by
  have hpiv := (r.normalized F).pivots_eq (s.normalized F)
    (r.normalized_valid F hr) (s.normalized_valid F hs)
  change r.sortedPivots = s.sortedPivots at hpiv
  have heq := (r.normalized F).normalized_eq (s.normalized F)
    (r.normalized_valid F hr) (s.normalized_valid F hs)
  funext p j
  by_cases hp : p ∈ r.pivots
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((r.mem_sortedPivots p).mpr hp)
    let row : Fin m := ⟨i, lt_of_lt_of_le hi r.sortedPivots_length_le⟩
    have hpi : r.sortedPivots[row.val]? = some p := by simp [row, hi, he]
    have hpi' : s.sortedPivots[row.val]? = some p := hpiv ▸ hpi
    simpa [r.normalized_apply F row p j hpi, s.normalized_apply F row p j hpi']
      using congrFun (congrFun heq row) j
  · have hp' : p ∉ s.pivots := by rwa [← r.pivots_eq s hr hs]
    simp [normalizedRow, r.row_zero_of_not_pivot p hp, s.row_zero_of_not_pivot p hp']

end FractionField

/-- The fraction-free artifact is unique up to row order and row scaling. No
division or fraction-field elements occur in the statement. -/
theorem RrefResult.equivalent_of_valid {A : Matrix (Fin m) (Fin n) R}
    (r s : RrefResult R m n) (hr : r.Valid A) (hs : s.Valid A) : r.Equivalent s := by
  refine ⟨r.pivots_eq s hr hs, ?_⟩
  intro p j
  by_cases hp : p ∈ r.pivots
  · have hp' : p ∈ s.pivots := by rwa [← r.pivots_eq s hr hs]
    have h := congrFun (congrFun (r.normalizedRow_eq (FractionRing R) s hr hs) p) j
    have hd : algebraMap R (FractionRing R) (r.row p p) ≠ 0 := by
      exact fun h => r.pivot_ne_zero hr p hp (IsFractionRing.to_map_eq_zero_iff.mp h)
    have hd' : algebraMap R (FractionRing R) (s.row p p) ≠ 0 := by
      exact fun h => s.pivot_ne_zero hs p hp' (IsFractionRing.to_map_eq_zero_iff.mp h)
    dsimp only [normalizedRow] at h
    have hc := (div_eq_div_iff hd hd').mp h
    apply IsFractionRing.injective R (FractionRing R)
    simpa only [map_mul, mul_comm] using hc
  · have hp' : p ∉ s.pivots := by rwa [← r.pivots_eq s hr hs]
    simp [r.row_zero_of_not_pivot p hp, s.row_zero_of_not_pivot p hp']

end Domain

end SympyProofs.Rref
