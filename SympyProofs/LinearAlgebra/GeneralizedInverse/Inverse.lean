module

public import SympyProofs.LinearAlgebra.Rref.FractionField
public import SympyProofs.LinearAlgebra.GeneralizedInverse.FieldInverse

/-! The canonical generalized inverse of a fraction-free augmented-RREF result.
Extraction looks up rows by their pivots and divides only when interpreting the
result in a fraction field. The stored certificate has no denominator or row order. -/

@[expose] public section

namespace SympyProofs.GeneralizedInverse

variable {R : Type*} [CommRing R] [IsDomain R] {m n : ℕ}
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

omit [IsDomain R] [IsFractionRing R F] in
/-- Augmentation commutes with mapping into the fraction field. -/
theorem augmentedIdentity_map (A : Matrix (Fin m) (Fin n) R) :
    (augmentedIdentity A).map (algebraMap R F) =
      augmentedIdentity (A.map (algebraMap R F)) := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [augmentedIdentity, Matrix.one_apply]

end SympyProofs.GeneralizedInverse

namespace SympyProofs.Rref

open SympyProofs.GeneralizedInverse

variable {R : Type*} [CommRing R] [IsDomain R] {m n : ℕ}
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Direct extraction: no row sorting, row permutation, or sum over physical rows.
Missing pivots give zero; each present pivot supplies its own scale. -/
def RrefResult.inverse (r : RrefResult R m (n + m)) : Matrix (Fin n) (Fin m) F :=
  fun j k => r.normalizedRow F (j.castAdd m) (Fin.natAdd n k)

omit [IsDomain R] [IsFractionRing R F] in
/-- Read an inverse entry directly from its stored pivot row. -/
theorem RrefResult.inverse_apply_lookup (r : RrefResult R m (n + m)) (j : Fin n) (k : Fin m) :
    r.inverse F j k = match r.lookup (j.castAdd m) with
      | none => 0
      | some row => algebraMap R F row[n + k.val] / algebraMap R F row[j.val] := by
  cases h : r.lookup (j.castAdd m) <;>
    simp [inverse, normalizedRow, row, h]

/-- The direct lookup formula agrees with the existing normalized-field theory. -/
theorem RrefResult.inverse_eq_normalized {A : Matrix (Fin m) (Fin n) R}
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    r.inverse F = (r.normalized F).inverse := by
  have hn := r.normalized_valid F hr
  ext j k
  change r.normalizedRow F (j.castAdd m) (Fin.natAdd n k) =
    (r.normalized F).pivotVector (fun i => (r.normalized F).matrix i (Fin.natAdd n k))
      (j.castAdd m)
  by_cases hp : j.castAdd m ∈ r.pivots
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((r.mem_sortedPivots _).mpr hp)
    let row : Fin m := ⟨i, lt_of_lt_of_le hi r.sortedPivots_length_le⟩
    have hpi : r.sortedPivots[row.val]? = some (j.castAdd m) := by simp [row, hi, he]
    rw [(r.normalized F).pivotVector_apply hn _ row _ hpi]
    simp [r.normalized_apply F row _ _ hpi]
  · have hp' : j.castAdd m ∉ (r.normalized F).pivots := by
      simpa [normalized] using hp
    rw [(r.normalized F).pivotVector_supported _ _ hp']
    simp [normalizedRow, r.row_zero_of_not_pivot _ hp]

/-- The same canonical support conditions, stated using the stored pivot set. -/
structure RrefResult.IsCanonicalInverse (r : RrefResult R m (n + m))
    (A : Matrix (Fin m) (Fin n) R) (G : Matrix (Fin n) (Fin m) F) : Prop where
  inner : A.map (algebraMap R F) * G * A.map (algebraMap R F) = A.map (algebraMap R F)
  zero_nonpivot_rows : ∀ j, j.castAdd m ∉ r.pivots → ∀ k, G j k = 0
  zero_right_pivot_columns : ∀ k, Fin.natAdd n k ∈ r.pivots → ∀ j, G j k = 0

omit [IsDomain R] [IsFractionRing R F] in
/-- The new support specification coincides with that of the canonical view. -/
theorem RrefResult.isCanonicalInverse_iff (r : RrefResult R m (n + m))
    (A : Matrix (Fin m) (Fin n) R) (G : Matrix (Fin n) (Fin m) F) :
    r.IsCanonicalInverse F A G ↔
      (r.normalized F).IsCanonicalInverse (A.map (algebraMap R F)) G := by
  constructor
  · intro h
    exact ⟨h.inner, by simpa [normalized] using h.zero_nonpivot_rows,
      by simpa [normalized] using h.zero_right_pivot_columns⟩
  · intro h
    exact ⟨h.inner, by simpa [normalized] using h.zero_nonpivot_rows,
      by simpa [normalized] using h.zero_right_pivot_columns⟩

theorem RrefResult.inverse_isCanonical (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    r.IsCanonicalInverse F A (r.inverse F) := by
  apply (r.isCanonicalInverse_iff F A _).mpr
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_isCanonical _ (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr)

/-- Both generalized-inverse identities hold over the fraction field. -/
theorem RrefResult.inverse_reflexive (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    Matrix.IsReflexiveGeneralizedInverse (A.map (algebraMap R F)) (r.inverse F) := by
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_reflexive _ (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr)

theorem RrefResult.mul_inverse_mul (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    A.map (algebraMap R F) * r.inverse F * A.map (algebraMap R F) = A.map (algebraMap R F) :=
  (r.inverse_reflexive F A hr).inner

theorem RrefResult.inverse_mul_inverse (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    r.inverse F * A.map (algebraMap R F) * r.inverse F = r.inverse F :=
  (r.inverse_reflexive F A hr).outer

theorem RrefResult.IsCanonicalInverse.eq_inverse
    {A : Matrix (Fin m) (Fin n) R} {r : RrefResult R m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G : Matrix (Fin n) (Fin m) F}
    (hG : r.IsCanonicalInverse F A G) : G = r.inverse F := by
  rw [r.inverse_eq_normalized F hr]
  exact ((r.isCanonicalInverse_iff F A G).mp hG).eq_inverse (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr)

theorem RrefResult.existsUnique_canonicalInverse (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    ∃! G, r.IsCanonicalInverse F A G :=
  ⟨r.inverse F, r.inverse_isCanonical F A hr, fun _ hG => hG.eq_inverse F hr⟩

theorem RrefResult.IsCanonicalInverse.unique
    {A : Matrix (Fin m) (Fin n) R} {r : RrefResult R m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G H : Matrix (Fin n) (Fin m) F}
    (hG : r.IsCanonicalInverse F A G) (hH : r.IsCanonicalInverse F A H) : G = H :=
  (hG.eq_inverse F hr).trans (hH.eq_inverse F hr).symm

/-- Valid algorithms, row orders, and independent nonzero row scales give the
same generalized inverse. -/
theorem RrefResult.inverse_eq (A : Matrix (Fin m) (Fin n) R)
    (r s : RrefResult R m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (hs : s.Valid (augmentedIdentity A)) :
    r.inverse F = s.inverse F := by
  ext j k
  exact congrFun (congrFun (r.normalizedRow_eq F s hr hs) (j.castAdd m)) (Fin.natAdd n k)

theorem RrefResult.inverse_range_iff (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) (x : Fin n → F) :
    (∃ b, (r.inverse F).mulVec b = x) ↔ ∀ j, j.castAdd m ∉ r.pivots → x j = 0 := by
  rw [r.inverse_eq_normalized F hr]
  simpa [normalized] using (r.normalized F).inverse_range_iff (A.map (algebraMap R F))
    (by simpa [augmentedIdentity_map] using r.normalized_valid F hr) x

theorem RrefResult.inverse_kernel_iff (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → F) :
    (r.inverse F).mulVec b = 0 ↔ ∀ k, Fin.natAdd n k ∉ r.pivots → b k = 0 := by
  rw [r.inverse_eq_normalized F hr]
  simpa [normalized] using (r.normalized F).inverse_kernel_iff (A.map (algebraMap R F))
    (by simpa [augmentedIdentity_map] using r.normalized_valid F hr) b

/-- The prescribed range depends only on the input over the fraction field. -/
theorem RrefResult.inverse_range_eq (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    LinearMap.range (r.inverse F).mulVecLin =
      Submodule.pi {j | ∃ x ∈ LinearMap.ker (A.map (algebraMap R F)).mulVecLin,
        IsGreatest (Function.support x) j} (fun _ => ⊥) := by
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_range_eq _ (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr)

/-- The prescribed kernel depends only on the input over the fraction field. -/
theorem RrefResult.inverse_ker_eq (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    LinearMap.ker (r.inverse F).mulVecLin =
      Submodule.pi {k | ∃ x ∈ LinearMap.range (A.map (algebraMap R F)).mulVecLin,
        IsGreatest (Function.support x) k} (fun _ => ⊥) := by
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_ker_eq _ (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr)

theorem RrefResult.inverse_solve_iff (A : Matrix (Fin m) (Fin n) R)
    (r : RrefResult R m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → F) :
    (A.map (algebraMap R F)).mulVec ((r.inverse F).mulVec b) = b ↔
      ∃ x, (A.map (algebraMap R F)).mulVec x = b := by
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_solve_iff _ (by
    simpa [augmentedIdentity_map] using r.normalized_valid F hr) b

theorem RrefResult.inverse_zero (r : RrefResult R m (n + m))
    (hr : r.Valid (augmentedIdentity (0 : Matrix (Fin m) (Fin n) R))) : r.inverse F = 0 := by
  have h := (r.inverse_reflexive F 0 hr).outer
  simpa using h.symm

theorem RrefResult.inverse_eq_of_inverse (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin n) F) (r : RrefResult R n (n + n))
    (hr : r.Valid (augmentedIdentity A))
    (hBA : B * A.map (algebraMap R F) = 1) (hAB : A.map (algebraMap R F) * B = 1) :
    r.inverse F = B := by
  rw [r.inverse_eq_normalized F hr]
  exact (r.normalized F).inverse_eq_of_inverse _ B
    (by simpa [augmentedIdentity_map] using r.normalized_valid F hr) hBA hAB

end SympyProofs.Rref

namespace SympyProofs.GeneralizedInverse

open SympyProofs.Rref

variable {R : Type*} [CommRing R] [IsDomain R] {m n : ℕ}
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Reduce over the integral domain, then interpret the inverse in a fraction field. -/
def inverseRref (rref : RrefOperation R) (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin n) (Fin m) F := (rref (augmentedIdentity A)).inverse F

theorem inverseRref_existsUnique (rref : RrefOperation R)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) R), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) R) :
    ∃! G, (rref (augmentedIdentity A)).IsCanonicalInverse F A G :=
  (rref (augmentedIdentity A)).existsUnique_canonicalInverse F A (valid _)

theorem inverseRref_reflexive (rref : RrefOperation R)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) R), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) R) :
    Matrix.IsReflexiveGeneralizedInverse (A.map (algebraMap R F)) (inverseRref F rref A) :=
  (rref (augmentedIdentity A)).inverse_reflexive F A (valid _)

theorem inverseRref_outer (rref : RrefOperation R)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) R), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) R) :
    inverseRref F rref A * A.map (algebraMap R F) * inverseRref F rref A =
      inverseRref F rref A := (inverseRref_reflexive F rref valid A).outer

theorem inverseRref_eq (rref₁ rref₂ : RrefOperation R)
    (valid₁ : ∀ {m n} (A : Matrix (Fin m) (Fin n) R), (rref₁ A).Valid A)
    (valid₂ : ∀ {m n} (A : Matrix (Fin m) (Fin n) R), (rref₂ A).Valid A)
    (A : Matrix (Fin m) (Fin n) R) : inverseRref F rref₁ A = inverseRref F rref₂ A :=
  (rref₁ (augmentedIdentity A)).inverse_eq F A (rref₂ (augmentedIdentity A))
    (valid₁ _) (valid₂ _)

end SympyProofs.GeneralizedInverse
