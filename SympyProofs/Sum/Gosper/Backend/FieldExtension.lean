module

public import SympyProofs.Sum.Gosper.Backend.Residual

/-! An RREF computed over the coefficient field can be used for right-hand sides
in an extension field. Identity augmentation makes the right block an invertible
row transformation, so its validity is preserved by the field embedding. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K L : Type*} {m n : ℕ}

/-- Embed the computed entries and denominator while retaining the pivot indices. -/
def RrefResult.map [CommRing K] [CommRing L]
    (r : RrefResult K m n) (f : K →+* L) : RrefResult L m n where
  matrix := r.matrix.map f
  denominator := f r.denominator
  pivots := r.pivots
  length_le := r.length_le

@[simp]
theorem RrefResult.map_id [CommRing K] (r : RrefResult K m n) :
    r.map (RingHom.id K) = r := by
  cases r
  rfl

variable [Field K] [Field L]

/-- Embedding preserves the pivot structure, independently of the original input matrix. -/
theorem RrefResult.map_valid_self {A : Matrix (Fin m) (Fin n) K}
    (r : RrefResult K m n) (hr : r.Valid A) (f : K →+* L) :
    (r.map f).Valid (r.map f).matrix where
  denominator_ne_zero := by
    simpa only [map, ne_eq, map_eq_zero] using hr.denominator_ne_zero
  ordered := hr.ordered
  pivot_column := by
    intro i j hp k
    change f (r.matrix k j) = if k = i then f r.denominator else 0
    rw [hr.pivot_column i j hp k]
    split_ifs <;> simp
  before_pivot := by
    intro i j hp k hkj
    change f (r.matrix i k) = 0
    rw [hr.before_pivot i j hp k hkj, map_zero]
  zero_row := by
    intro i hp
    ext j
    change f (r.matrix i j) = 0
    rw [hr.zero_row i hp]
    exact map_zero f
  kernel_iff _ := Iff.rfl

/-- Every valid reduction of `[A | I]` supplies a solution to every attainable right-hand side. -/
theorem RrefResult.inverse_solve_iff (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → K) :
    A.mulVec (r.inverse.mulVec b) = b ↔ ∃ x, A.mulVec x = b := by
  constructor
  · exact fun hb => ⟨r.inverse.mulVec b, hb⟩
  · rintro ⟨x, rfl⟩
    have he : r.leftMatrix.mulVec x = r.rightMatrix.mulVec (A.mulVec x) := by
      have hk := (hr.kernel_iff (Fin.addCases x (-A.mulVec x))).mp
        (by rw [augmentedIdentity_mulVec, sub_self])
      rwa [RrefResult.mulVec_addCases, sub_eq_zero] at hk
    have hk : r.matrix.mulVec (Fin.addCases (r.inverse.mulVec (A.mulVec x))
        (-A.mulVec x)) = 0 := by
      rw [RrefResult.mulVec_addCases, RrefResult.inverse_mulVec, ← he,
        RrefResult.leftSolution_mulVec A r hr, sub_self]
    have ha := (hr.kernel_iff _).mpr hk
    rwa [augmentedIdentity_mulVec, sub_eq_zero] at ha

/-- Identity augmentation records the row transformation in the right block. -/
theorem RrefResult.matrix_eq_rightMatrix_mul (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    r.matrix = r.rightMatrix * augmentedIdentity A := by
  have hleft : r.leftMatrix = r.rightMatrix * A := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    have hk := (hr.kernel_iff (Fin.addCases x (-A.mulVec x))).mp
      (by rw [augmentedIdentity_mulVec, sub_self])
    rw [RrefResult.mulVec_addCases, sub_eq_zero] at hk
    simpa only [Matrix.mulVec_mulVec] using hk
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [leftMatrix, Matrix.mul_apply, augmentedIdentity, Fin.addCases_left]
      using congrFun (congrFun hleft i) j
  · simp [Matrix.mul_apply, augmentedIdentity, Matrix.one_apply, rightMatrix]

/-- The right block of a valid reduction of `[A | I]` is invertible. -/
theorem RrefResult.rightMatrix_isUnit (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    IsUnit r.rightMatrix := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro b c hbc
  have hz : r.rightMatrix.mulVec (b - c) = 0 := by
    rw [Matrix.mulVec_sub, hbc, sub_self]
  have hk : r.matrix.mulVec (Fin.addCases 0 (-(b - c))) = 0 := by
    rw [RrefResult.mulVec_addCases, Matrix.mulVec_zero, hz, sub_self]
  have hb := (hr.kernel_iff _).mpr hk
  simpa only [augmentedIdentity_mulVec, Matrix.mulVec_zero, zero_sub,
    neg_eq_zero, sub_eq_zero] using hb

/-- Mapping an identity augmentation is the identity augmentation of the mapped matrix. -/
theorem augmentedIdentity_map (A : Matrix (Fin m) (Fin n) K) (f : K →+* L) :
    (augmentedIdentity A).map f = augmentedIdentity (A.map f) := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [augmentedIdentity]
  · simp [augmentedIdentity, Matrix.one_apply]

/-- The reduction computed over `K` remains valid for the same coefficient matrix over `L`. -/
theorem RrefResult.map_valid_augmentedIdentity (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (f : K →+* L) :
    (r.map f).Valid (augmentedIdentity (A.map f)) where
  denominator_ne_zero := by
    simpa only [map, ne_eq, map_eq_zero] using hr.denominator_ne_zero
  ordered := hr.ordered
  pivot_column := by
    intro i j hp k
    change f (r.matrix k j) = if k = i then f r.denominator else 0
    rw [hr.pivot_column i j hp k]
    split_ifs <;> simp
  before_pivot := by
    intro i j hp k hkj
    change f (r.matrix i k) = 0
    rw [hr.before_pivot i j hp k hkj, map_zero]
  zero_row := by
    intro i hp
    ext j
    change f (r.matrix i j) = 0
    rw [hr.zero_row i hp]
    exact map_zero f
  kernel_iff := by
    intro x
    have hunit : IsUnit (r.rightMatrix.map f) :=
      (r.rightMatrix_isUnit A hr).map f.mapMatrix
    have he : (r.map f).matrix =
        r.rightMatrix.map f * augmentedIdentity (A.map f) := by
      change r.matrix.map f = _
      rw [r.matrix_eq_rightMatrix_mul A hr, Matrix.map_mul, augmentedIdentity_map]
    rw [he, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      rw [hx, Matrix.mulVec_zero]
    · intro hx
      apply Matrix.mulVec_injective_of_isUnit hunit
      simpa only [Matrix.mulVec_zero] using hx

end Gosper.Algorithm
