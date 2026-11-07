module

public import Mathlib

/-! Normalized field-valued RREF, used as a mathematical view of fraction-free data.
Canonical pivot coordinates and uniqueness follow from kernel equivalence. -/

@[expose] public section

namespace SympyProofs.Rref

structure NormalizedRref (K : Type*) (m n : ℕ) where
  matrix : Matrix (Fin m) (Fin n) K
  pivots : List (Fin n)
  /-- Each pivot corresponds to a row of the matrix. -/
  length_le : pivots.length ≤ m

/-- The matrix primitive returns a pivot list with its structural row bound.
Its algebraic correctness contract is separate from the operation. -/
abbrev NormalizedRrefOperation (K : Type*) :=
  {m n : ℕ} → Matrix (Fin m) (Fin n) K → NormalizedRref K m n

variable {K : Type*} [Field K] {m n : ℕ}

/-- The matrix is in normalized RREF. The pivot list enumerates the leading
columns of the nonzero rows, in row order. Equality of
kernels is the row-equivalence property needed for an augmented system. -/
structure NormalizedRref.Valid (A : Matrix (Fin m) (Fin n) K) (r : NormalizedRref K m n) : Prop where
  ordered : r.pivots.Pairwise (· < ·)
  pivot_column : ∀ (i : Fin m) (j : Fin n), r.pivots[i.val]? = some j →
    ∀ k : Fin m, r.matrix k j = if k = i then (1 : K) else 0
  before_pivot : ∀ (i : Fin m) (j : Fin n), r.pivots[i.val]? = some j →
    ∀ k < j, r.matrix i k = 0
  zero_row : ∀ i : Fin m, r.pivots[i.val]? = none → r.matrix i = 0
  kernel_iff : ∀ x : Fin n → K, A.mulVec x = 0 ↔ r.matrix.mulVec x = 0

/-- Kernel equivalence also preserves equality of images. -/
theorem NormalizedRref.mulVec_eq_iff {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (x y : Fin n → K) :
    A.mulVec x = A.mulVec y ↔ r.matrix.mulVec x = r.matrix.mulVec y := by
  simpa only [Matrix.mulVec_sub, sub_eq_zero] using hr.kernel_iff (x - y)

/-- A vector is supported on the pivot columns. -/
def NormalizedRref.PivotSupported (r : NormalizedRref K m n) (x : Fin n → K) : Prop :=
  ∀ j, j ∉ r.pivots → x j = 0

/-- Insert row values into pivot coordinates. -/
def NormalizedRref.pivotVector (r : NormalizedRref K m n) (y : Fin m → K) : Fin n → K :=
  fun j => ∑ i : Fin m, if r.pivots[i.val]? = some j then y i else 0

theorem NormalizedRref.pivotVector_supported (r : NormalizedRref K m n) (y : Fin m → K) :
    r.PivotSupported (r.pivotVector y) := by
  intro j hj
  have hp (i : Fin m) : r.pivots[i.val]? ≠ some j :=
    fun h => hj (List.mem_of_getElem? h)
  simp [pivotVector, hp]

theorem NormalizedRref.pivotVector_apply {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (y : Fin m → K)
    (i : Fin m) (j : Fin n) (hp : r.pivots[i.val]? = some j) :
    r.pivotVector y j = y i := by
  unfold pivotVector
  rw [Finset.sum_eq_single i]
  · simp [hp]
  · intro k _ hki
    have hne : r.pivots[k.val]? ≠ some j := by
      intro hk
      apply hki
      apply Fin.ext
      exact hr.ordered.nodup.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp hk).1
        (hk.trans hp.symm)
    simp [hne]
  · simp

/-- Pivot columns reconstruct every vector in the column space. -/
theorem NormalizedRref.mulVec_pivotVector {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (x : Fin n → K) :
    r.matrix.mulVec (r.pivotVector (r.matrix.mulVec x)) = r.matrix.mulVec x := by
  ext k
  simp only [Matrix.mulVec, dotProduct, pivotVector, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin m, if k = i then ∑ j, r.matrix i j * x j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hp : r.pivots[i.val]? with
      | none => simp [hr.zero_row i hp]
      | some p =>
        simp only [Option.some.injEq, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte]
        rw [hr.pivot_column i p hp k]
        split_ifs
        · simp
        · simp
    _ = _ := by simp

/-- Kernel equivalence transports pivot reconstruction back to the input matrix. -/
theorem NormalizedRref.input_mulVec_pivotVector {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (x : Fin n → K) :
    A.mulVec (r.pivotVector (r.matrix.mulVec x)) = A.mulVec x := by
  have h := (hr.kernel_iff (r.pivotVector (r.matrix.mulVec x) - x)).mpr (by
    rw [Matrix.mulVec_sub, r.mulVec_pivotVector hr, sub_self])
  rwa [Matrix.mulVec_sub, sub_eq_zero] at h

/-- On pivot-supported vectors, each pivot row reads just its pivot coordinate. -/
theorem NormalizedRref.mulVec_of_supported {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (x : Fin n → K)
    (hx : r.PivotSupported x) (i : Fin m) (p : Fin n)
    (hp : r.pivots[i.val]? = some p) :
    r.matrix.mulVec x i = x p := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single p]
  · simp [hr.pivot_column i p hp i]
  · intro j _ hj
    by_cases hm : j ∈ r.pivots
    · obtain ⟨k, hk, he⟩ := List.getElem_of_mem hm
      let row : Fin m := ⟨k, lt_of_lt_of_le hk r.length_le⟩
      have hp' : r.pivots[row.val]? = some j := by simp [row, hk, he]
      have hrow : i ≠ row := by
        intro hi
        have hp'' : r.pivots[i.val]? = some j := hi ▸ hp'
        exact hj (Option.some.inj (hp''.symm.trans hp))
      rw [hr.pivot_column row j hp' i, ite_eq_right hrow, zero_mul]
    · rw [hx j hm, mul_zero]
  · simp

/-- The input matrix is injective when restricted to pivot coordinates. -/
theorem NormalizedRref.eq_zero_of_supported_of_mulVec_eq_zero
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m n) (hr : r.Valid A)
    (x : Fin n → K) (hx : r.PivotSupported x) (h : A.mulVec x = 0) : x = 0 := by
  have hk := (hr.kernel_iff x).mp h
  funext j
  by_cases hj : j ∈ r.pivots
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hj
    let row : Fin m := ⟨i, lt_of_lt_of_le hi r.length_le⟩
    have hp : r.pivots[row.val]? = some j := by simp [row, hi, he]
    have hz := congrFun hk row
    rw [r.mulVec_of_supported hr x hx row j hp] at hz
    exact by simpa using hz
  · exact hx j hj

/-- A pivot column cannot be expressed using preceding columns. This kernel
characterization makes pivot positions independent of the RREF implementation. -/
theorem NormalizedRref.mem_pivots_iff {A : Matrix (Fin m) (Fin n) K}
    (r : NormalizedRref K m n) (hr : r.Valid A) (j : Fin n) :
    j ∈ r.pivots ↔ ∀ x : Fin n → K, A.mulVec x = 0 →
      (∀ k, j < k → x k = 0) → x j = 0 := by
  constructor
  · intro hj x hx hafter
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hj
    let row : Fin m := ⟨i, lt_of_lt_of_le hi r.length_le⟩
    have hp : r.pivots[row.val]? = some j := by simp [row, hi, he]
    have hrow : r.matrix.mulVec x row = x j := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · simp [hr.pivot_column row j hp row]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · rw [hr.before_pivot row j hp k hlt, zero_mul]
        · rw [hafter k hgt, mul_zero]
      · simp
    have hz := congrFun ((hr.kernel_iff x).mp hx) row
    rw [hrow] at hz
    exact by simpa using hz
  · intro h
    by_contra hj
    let e : Fin n → K := Pi.single j 1
    let v := r.pivotVector (r.matrix.mulVec e)
    have hk : A.mulVec (e - v) = 0 := by
      rw [Matrix.mulVec_sub, r.input_mulVec_pivotVector hr e, sub_self]
    have hafter : ∀ k, j < k → (e - v) k = 0 := by
      intro k hjk
      have hv : v k = 0 := by
        dsimp [v, pivotVector]
        apply Finset.sum_eq_zero
        intro i _
        split_ifs with hp
        · have heq : r.matrix.mulVec e i = r.matrix i j := by
            simp [e, Matrix.col]
          rw [heq, hr.before_pivot i k hp j hjk]
        · rfl
      simp [e, hv, ne_of_gt hjk]
    have hz := h (e - v) hk hafter
    have hv : v j = 0 := r.pivotVector_supported (r.matrix.mulVec e) j hj
    change e j - v j = 0 at hz
    rw [hv, sub_zero] at hz
    simp [e] at hz

/-- All valid RREF results for the same matrix have exactly the same ordered pivots. -/
theorem NormalizedRref.pivots_eq {A : Matrix (Fin m) (Fin n) K}
    (r s : NormalizedRref K m n) (hr : r.Valid A) (hs : s.Valid A) :
    r.pivots = s.pivots := by
  apply hr.ordered.eq_of_mem_iff hs.ordered
  intro j
  rw [r.mem_pivots_iff hr, s.mem_pivots_iff hs]

/-- Choosing zero free coordinates gives the same representative for every valid
normalized RREF result. -/
theorem NormalizedRref.pivotVector_mulVec_eq {A : Matrix (Fin m) (Fin n) K}
    (r s : NormalizedRref K m n) (hr : r.Valid A) (hs : s.Valid A) (x : Fin n → K) :
    r.pivotVector (r.matrix.mulVec x) = s.pivotVector (s.matrix.mulVec x) := by
  apply sub_eq_zero.mp
  apply r.eq_zero_of_supported_of_mulVec_eq_zero hr
  · intro j hj
    have hj' : j ∉ s.pivots := by rwa [← r.pivots_eq s hr hs]
    simp [r.pivotVector_supported _ j hj, s.pivotVector_supported _ j hj']
  · rw [Matrix.mulVec_sub, r.input_mulVec_pivotVector hr,
      s.input_mulVec_pivotVector hs, sub_self]

/-- The normalized RREF matrix is unique. -/
theorem NormalizedRref.normalized_eq {A : Matrix (Fin m) (Fin n) K}
    (r s : NormalizedRref K m n) (hr : r.Valid A) (hs : s.Valid A) :
    r.matrix = s.matrix := by
  have hpiv := r.pivots_eq s hr hs
  ext i j
  cases hp : r.pivots[i.val]? with
  | none =>
    have hp' : s.pivots[i.val]? = none := hpiv ▸ hp
    simp [hr.zero_row i hp, hs.zero_row i hp']
  | some p =>
    have hp' : s.pivots[i.val]? = some p := hpiv ▸ hp
    have h := congrFun (r.pivotVector_mulVec_eq s hr hs (Pi.single j 1)) p
    rw [r.pivotVector_apply hr _ i p hp, s.pivotVector_apply hs _ i p hp'] at h
    simpa [Matrix.mulVec_single_one, Matrix.col, div_eq_mul_inv, mul_comm] using h

end SympyProofs.Rref
