module

public import SympyProofs.LinearAlgebra.GeneralizedInverse.Basic
public import SympyProofs.LinearAlgebra.Rref.Normalized

/-! The canonical reflexive generalized inverse obtained from the **full** RREF
of `[A | I]`. It works over any field, with no rank or shape assumptions.

If `P` is the set of pivots in `A` and `Q` the set of pivots in the appended
identity, the additional canonical conditions are: rows outside `P` are zero,
and columns in `Q` are zero. Together with `A * G * A = A`, these conditions
uniquely determine `G` and imply `G * A * G = G`. The second support condition
specifies the action on inconsistent right-hand sides.

Reducing only the coefficient block does not impose the second condition:
the `NormalizedRref.Valid (augmentedIdentity A)` contract is for the full
augmented matrix, including its right-block pivots. -/

@[expose] public section

namespace SympyProofs.GeneralizedInverse

variable {K : Type*} {m n : ℕ}

/-- Append the identity on the right, with coefficient columns ordered first. -/
def augmentedIdentity [Semiring K] (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin m) (Fin (n + m)) K :=
  fun i => Fin.addCases (A i) ((1 : Matrix (Fin m) (Fin m) K) i)

variable [Field K]

theorem augmentedIdentity_mulVec (A : Matrix (Fin m) (Fin n) K)
    (x : Fin n → K) (b : Fin m → K) :
    (augmentedIdentity A).mulVec (Fin.addCases x b) = A.mulVec x + b := by
  ext i
  simp [augmentedIdentity, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]

theorem augmentedIdentity_mulVec_split (A : Matrix (Fin m) (Fin n) K)
    (v : Fin (n + m) → K) :
    (augmentedIdentity A).mulVec v =
      A.mulVec (fun j => v (j.castAdd m)) + fun k => v (Fin.natAdd n k) := by
  ext i
  simp [augmentedIdentity, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]

end SympyProofs.GeneralizedInverse

namespace SympyProofs.Rref

open SympyProofs.GeneralizedInverse

variable {K : Type*} [Field K] {m n : ℕ}

/-- Left-block pivots are columns independent of their predecessors: in a
dependence supported through `j`, the coefficient at `j` must vanish. -/
theorem NormalizedRref.castAdd_mem_pivots_iff
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (j : Fin n) :
    j.castAdd m ∈ r.pivots ↔
      ∀ x, A.mulVec x = 0 → (∀ k, j < k → x k = 0) → x j = 0 := by
  rw [r.mem_pivots_iff hr]
  constructor
  · intro hp x hx hafter
    have h := hp (Fin.addCases x 0) (by simp [augmentedIdentity_mulVec, hx]) (by
      intro k
      refine Fin.addCases (fun k hk => ?_) (fun k _ => ?_) k
      · simpa using hafter k (by simpa only [Fin.lt_def, Fin.val_castAdd] using hk)
      · simp)
    simpa using h
  · intro hp v hv hafter
    have hright : (fun k : Fin m => v (Fin.natAdd n k)) = 0 := by
      funext k
      exact hafter _ (by simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega)
    apply hp (fun k => v (k.castAdd m))
    · simpa only [augmentedIdentity_mulVec_split, hright, add_zero] using hv
    · intro k hk
      exact hafter _ (by simpa only [Fin.lt_def, Fin.val_castAdd] using hk)

/-- A right-block coordinate `k` is a pivot exactly when every vector in the
column space of `A` supported through `k` vanishes at `k`. -/
theorem NormalizedRref.natAdd_mem_pivots_iff
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (k : Fin m) :
    Fin.natAdd n k ∈ r.pivots ↔
      ∀ x, (∀ l, k < l → A.mulVec x l = 0) → A.mulVec x k = 0 := by
  rw [r.mem_pivots_iff hr]
  constructor
  · intro hp x hafter
    have h := hp (Fin.addCases x (-A.mulVec x)) (by simp [augmentedIdentity_mulVec]) (by
      intro j
      refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) j
      · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hj
        omega
      · have hkj : k < j := by
          simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hj
        simp [hafter j hkj])
    simpa using h
  · intro hp v hv hafter
    let x : Fin n → K := fun j => v (j.castAdd m)
    have he (l : Fin m) : A.mulVec x l + v (Fin.natAdd n l) = 0 := by
      simpa only [augmentedIdentity_mulVec_split, Pi.add_apply, Pi.zero_apply] using congrFun hv l
    have hx : A.mulVec x k = 0 := hp x (by
      intro l hkl
      have hz : v (Fin.natAdd n l) = 0 := hafter _ (by
        simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hkl)
      simpa only [hz, add_zero] using he l)
    simpa only [hx, zero_add] using he k

/-- Read normalized rows of the right block into the left pivot coordinates;
all nonpivot coefficient rows are zero. The result has shape `n × m`. -/
def NormalizedRref.inverse (r : NormalizedRref K m (n + m)) : Matrix (Fin n) (Fin m) K :=
  fun j k => ∑ i : Fin m, if r.pivots[i.val]? = some (j.castAdd m) then
    r.matrix i (Fin.natAdd n k) else 0

/-- Extraction is the left part of the full pivot-coordinate representative. -/
theorem NormalizedRref.inverse_mulVec_eq_pivotVector (r : NormalizedRref K m (n + m))
    (b : Fin m → K) (j : Fin n) :
    r.inverse.mulVec b j =
      r.pivotVector (r.matrix.mulVec (Fin.addCases (0 : Fin n → K) b)) (j.castAdd m) := by
  simp only [inverse, pivotVector, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : r.pivots[i.val]? = some (j.castAdd m)
  · simp [hp]
  · simp [hp]

/-- Coefficient-only inputs have zero right-pivot coordinates. -/
theorem NormalizedRref.pivotVector_coefficient_right_eq_zero
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (x : Fin n → K) (k : Fin m) :
    r.pivotVector (r.matrix.mulVec (Fin.addCases x (0 : Fin m → K)))
      (Fin.natAdd n k) = 0 := by
  by_cases hk : Fin.natAdd n k ∈ r.pivots
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hk
    let row : Fin m := ⟨i, lt_of_lt_of_le hi r.length_le⟩
    have hp : r.pivots[row.val]? = some (Fin.natAdd n k) := by simp [row, hi, he]
    rw [r.pivotVector_apply hr _ row _ hp]
    have hz (j : Fin n) : r.matrix row (j.castAdd m) = 0 := by
      apply hr.before_pivot row (Fin.natAdd n k) hp
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, hz]
  · exact r.pivotVector_supported _ _ hk

/-- A valid augmented RREF gives an inner inverse without any rank assumption. -/
theorem NormalizedRref.mul_inverse_mul (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    A * r.inverse * A = A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  have he : r.matrix.mulVec (Fin.addCases (0 : Fin n → K) (A.mulVec x)) =
      r.matrix.mulVec (Fin.addCases x (0 : Fin m → K)) := by
    apply (r.mulVec_eq_iff hr _ _).mp
    simp [augmentedIdentity_mulVec]
  have hleft :
      (fun j => r.pivotVector (r.matrix.mulVec (Fin.addCases x (0 : Fin m → K)))
        (j.castAdd m)) = r.inverse.mulVec (A.mulVec x) := by
    funext j
    rw [r.inverse_mulVec_eq_pivotVector, he]
  have hright :
      (fun k => r.pivotVector (r.matrix.mulVec (Fin.addCases x (0 : Fin m → K)))
        (Fin.natAdd n k)) = 0 := funext (r.pivotVector_coefficient_right_eq_zero hr x)
  have h := r.input_mulVec_pivotVector hr (Fin.addCases x (0 : Fin m → K))
  rw [augmentedIdentity_mulVec_split, hleft, hright, add_zero,
    augmentedIdentity_mulVec, add_zero] at h
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h


/-- The RREF normalization of a generalized inverse. Both support conditions
are needed: the first fixes its range, the second fixes its kernel. -/
structure NormalizedRref.IsCanonicalInverse (r : NormalizedRref K m (n + m))
    (A : Matrix (Fin m) (Fin n) K) (G : Matrix (Fin n) (Fin m) K) : Prop where
  inner : A * G * A = A
  zero_nonpivot_rows : ∀ j, j.castAdd m ∉ r.pivots → ∀ k, G j k = 0
  zero_right_pivot_columns : ∀ k, Fin.natAdd n k ∈ r.pivots → ∀ j, G j k = 0

theorem NormalizedRref.inverse_zero_nonpivot_row (r : NormalizedRref K m (n + m))
    (j : Fin n) (hj : j.castAdd m ∉ r.pivots) (k : Fin m) : r.inverse j k = 0 := by
  have hp (i : Fin m) : r.pivots[i.val]? ≠ some (j.castAdd m) :=
    fun h => hj (List.mem_of_getElem? h)
  simp [inverse, hp]

theorem NormalizedRref.inverse_zero_right_pivot_column
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (k : Fin m)
    (hk : Fin.natAdd n k ∈ r.pivots) (j : Fin n) : r.inverse j k = 0 := by
  obtain ⟨t, ht, he⟩ := List.getElem_of_mem hk
  let row : Fin m := ⟨t, lt_of_lt_of_le ht r.length_le⟩
  have hp : r.pivots[row.val]? = some (Fin.natAdd n k) := by simp [row, ht, he]
  unfold inverse
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · have hir : i ≠ row := by
      intro hir
      rw [hir, hp] at hi
      have hval := congrArg Fin.val (Option.some.inj hi)
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    rw [hr.pivot_column row (Fin.natAdd n k) hp i, ite_eq_right hir]
  · rfl

/-- The original matrix has trivial kernel on the selected coefficient coordinates. -/
theorem NormalizedRref.left_supported_eq_zero
    {A : Matrix (Fin m) (Fin n) K} (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (x : Fin n → K)
    (hx : ∀ j, j.castAdd m ∉ r.pivots → x j = 0) (h : A.mulVec x = 0) : x = 0 := by
  have hz : Fin.addCases x (0 : Fin m → K) = (0 : Fin (n + m) → K) := by
    apply r.eq_zero_of_supported_of_mulVec_eq_zero hr
    · intro j
      refine Fin.addCases (fun j hj => ?_) (fun k _ => ?_) j
      · simpa using hx j hj
      · simp
    · simpa using (augmentedIdentity_mulVec A x 0).trans (by simpa using h)
  funext j
  simpa using congrFun hz (j.castAdd m)

theorem NormalizedRref.inverse_isCanonical (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    r.IsCanonicalInverse A r.inverse :=
  ⟨r.mul_inverse_mul A hr, r.inverse_zero_nonpivot_row,
    r.inverse_zero_right_pivot_column hr⟩

/-- Every canonical inverse recovers a vector already supported on left pivots. -/
theorem NormalizedRref.IsCanonicalInverse.mulVec_of_supported
    {A : Matrix (Fin m) (Fin n) K} {r : NormalizedRref K m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G : Matrix (Fin n) (Fin m) K}
    (hG : r.IsCanonicalInverse A G) (x : Fin n → K)
    (hx : ∀ j, j.castAdd m ∉ r.pivots → x j = 0) :
    G.mulVec (A.mulVec x) = x := by
  apply sub_eq_zero.mp
  apply r.left_supported_eq_zero hr
  · intro j hj
    change (∑ k, G j k * A.mulVec x k) - x j = 0
    simp [hG.zero_nonpivot_rows j hj, hx j hj]
  · rw [Matrix.mulVec_sub]
    have hi := congrArg (fun M : Matrix (Fin m) (Fin n) K => M.mulVec x) hG.inner
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, sub_eq_zero] using hi

/-- The support normalization forces the second generalized-inverse identity. -/
theorem NormalizedRref.IsCanonicalInverse.reflexive
    {A : Matrix (Fin m) (Fin n) K} {r : NormalizedRref K m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G : Matrix (Fin n) (Fin m) K}
    (hG : r.IsCanonicalInverse A G) : Matrix.IsReflexiveGeneralizedInverse A G := by
  refine ⟨hG.inner, ?_⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro b
  have h := hG.mulVec_of_supported hr (G.mulVec b) (by
    intro j hj
    simp [Matrix.mulVec, dotProduct, hG.zero_nonpivot_rows j hj])
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h

/-- In particular, the inverse extracted by the augmented RREF is reflexive. -/
theorem NormalizedRref.inverse_reflexive (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    Matrix.IsReflexiveGeneralizedInverse A r.inverse :=
  (r.inverse_isCanonical A hr).reflexive hr

/-- An inner inverse with the two prescribed support conditions is unique. -/
theorem NormalizedRref.IsCanonicalInverse.eq_inverse
    {A : Matrix (Fin m) (Fin n) K} {r : NormalizedRref K m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G : Matrix (Fin n) (Fin m) K}
    (hG : r.IsCanonicalInverse A G) : G = r.inverse := by
  apply Matrix.ext_iff_mulVec.mpr
  intro b
  let v := r.pivotVector (r.matrix.mulVec (Fin.addCases (0 : Fin n → K) b))
  let x : Fin n → K := fun j => v (j.castAdd m)
  let z : Fin m → K := fun k => v (Fin.natAdd n k)
  have hv := r.pivotVector_supported (r.matrix.mulVec (Fin.addCases (0 : Fin n → K) b))
  have hx : ∀ j, j.castAdd m ∉ r.pivots → x j = 0 :=
    fun j hj => hv (j.castAdd m) hj
  have hz : G.mulVec z = 0 := by
    ext j
    change ∑ k, G j k * z k = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : Fin.natAdd n k ∈ r.pivots
    · rw [hG.zero_right_pivot_columns k hk j, zero_mul]
    · have hzk : z k = 0 := hv (Fin.natAdd n k) hk
      rw [hzk, mul_zero]
  have hb : A.mulVec x + z = b := by
    have h := r.input_mulVec_pivotVector hr (Fin.addCases (0 : Fin n → K) b)
    ext i
    simpa [augmentedIdentity, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
      Matrix.one_apply, x, z, v] using congrFun h i
  calc
    G.mulVec b = G.mulVec (A.mulVec x + z) := congrArg G.mulVec hb.symm
    _ = x := by rw [Matrix.mulVec_add, hG.mulVec_of_supported hr x hx, hz, add_zero]
    _ = r.inverse.mulVec b := by
      funext j
      exact (r.inverse_mulVec_eq_pivotVector b j).symm

theorem NormalizedRref.IsCanonicalInverse.unique
    {A : Matrix (Fin m) (Fin n) K} {r : NormalizedRref K m (n + m)}
    (hr : r.Valid (augmentedIdentity A)) {G H : Matrix (Fin n) (Fin m) K}
    (hG : r.IsCanonicalInverse A G) (hH : r.IsCanonicalInverse A H) : G = H :=
  (hG.eq_inverse hr).trans (hH.eq_inverse hr).symm

/-- Existence and uniqueness for every rectangular or singular input with a valid
augmented RREF certificate. Reflexivity follows, so need not be assumed here. -/
theorem NormalizedRref.existsUnique_canonicalInverse (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    ∃! G, r.IsCanonicalInverse A G :=
  ⟨r.inverse, r.inverse_isCanonical A hr, fun _ hG => hG.eq_inverse hr⟩

/-- The normalized RREF certificate does not change the generalized inverse. -/
theorem NormalizedRref.inverse_eq (A : Matrix (Fin m) (Fin n) K)
    (r s : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity A)) (hs : s.Valid (augmentedIdentity A)) :
    r.inverse = s.inverse := by
  apply Matrix.ext_iff_mulVec.mpr
  intro b
  funext j
  rw [r.inverse_mulVec_eq_pivotVector, s.inverse_mulVec_eq_pivotVector,
    r.pivotVector_mulVec_eq s hr hs]

/-- The range is exactly the coordinate subspace spanned by left pivot columns. -/
theorem NormalizedRref.inverse_range_iff (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (x : Fin n → K) :
    (∃ b, r.inverse.mulVec b = x) ↔ ∀ j, j.castAdd m ∉ r.pivots → x j = 0 := by
  constructor
  · rintro ⟨b, rfl⟩ j hj
    simp [Matrix.mulVec, dotProduct, r.inverse_zero_nonpivot_row j hj]
  · intro hx
    exact ⟨A.mulVec x, (r.inverse_isCanonical A hr).mulVec_of_supported hr x hx⟩

/-- The residual lies in the coordinate subspace spanned by right-block pivots. -/
theorem NormalizedRref.inverse_residual_supported (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → K)
    (k : Fin m) (hk : Fin.natAdd n k ∉ r.pivots) :
    (b - A.mulVec (r.inverse.mulVec b)) k = 0 := by
  let v := r.pivotVector (r.matrix.mulVec (Fin.addCases (0 : Fin n → K) b))
  have hleft : (fun j => v (j.castAdd m)) = r.inverse.mulVec b := by
    funext j
    exact (r.inverse_mulVec_eq_pivotVector b j).symm
  have h := r.input_mulVec_pivotVector hr (Fin.addCases (0 : Fin n → K) b)
  rw [augmentedIdentity_mulVec_split, hleft, augmentedIdentity_mulVec] at h
  have hi := congrFun h k
  have hz : v (Fin.natAdd n k) = 0 := r.pivotVector_supported _ _ hk
  change A.mulVec (r.inverse.mulVec b) k + v (Fin.natAdd n k) =
    A.mulVec 0 k + b k at hi
  simp only [hz, add_zero, Matrix.mulVec_zero, Pi.zero_apply, zero_add] at hi
  exact sub_eq_zero.mpr hi.symm

/-- The kernel is exactly the coordinate subspace spanned by right-block pivots.
This fixes the otherwise undetermined action on inconsistent right-hand sides. -/
theorem NormalizedRref.inverse_kernel_iff (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → K) :
    r.inverse.mulVec b = 0 ↔ ∀ k, Fin.natAdd n k ∉ r.pivots → b k = 0 := by
  constructor
  · intro h k hk
    simpa [h] using r.inverse_residual_supported A hr b k hk
  · intro hb
    ext j
    change ∑ k, r.inverse j k * b k = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : Fin.natAdd n k ∈ r.pivots
    · rw [r.inverse_zero_right_pivot_column hr k hk j, zero_mul]
    · rw [hb k hk, mul_zero]

private theorem isGreatest_support_iff {ι : Type*} [LinearOrder ι] (x : ι → K) (i : ι) :
    IsGreatest (Function.support x) i ↔ x i ≠ 0 ∧ ∀ j, i < j → x j = 0 := by
  constructor
  · rintro ⟨hi, hmax⟩
    refine ⟨hi, fun j hij => ?_⟩
    by_contra hj
    exact (not_le_of_gt hij) (hmax hj)
  · rintro ⟨hi, hafter⟩
    refine ⟨hi, ?_⟩
    intro j hj
    by_contra hji
    exact hj (hafter j (lt_of_not_ge hji))

/-- The range vanishes at every last nonzero coordinate of a vector in the input's kernel. -/
theorem NormalizedRref.inverse_range_eq (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    LinearMap.range r.inverse.mulVecLin =
      Submodule.pi {j | ∃ x ∈ LinearMap.ker A.mulVecLin,
        IsGreatest (Function.support x) j} (fun _ => ⊥) := by
  ext x
  simp [r.inverse_range_iff A hr, Submodule.mem_pi, r.castAdd_mem_pivots_iff hr,
    isGreatest_support_iff, not_forall, not_imp, and_comm, and_left_comm]

/-- The kernel vanishes at every last nonzero coordinate of a vector in the input's range. -/
theorem NormalizedRref.inverse_ker_eq (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) :
    LinearMap.ker r.inverse.mulVecLin =
      Submodule.pi {k | ∃ x ∈ LinearMap.range A.mulVecLin,
        IsGreatest (Function.support x) k} (fun _ => ⊥) := by
  ext b
  simp [r.inverse_kernel_iff A hr, Submodule.mem_pi, r.natAdd_mem_pivots_iff hr,
    isGreatest_support_iff, not_forall, not_imp, and_comm, and_left_comm]

/-- Multiplying by the extracted inverse solves exactly the consistent systems. -/
theorem NormalizedRref.inverse_solve_iff (A : Matrix (Fin m) (Fin n) K)
    (r : NormalizedRref K m (n + m)) (hr : r.Valid (augmentedIdentity A)) (b : Fin m → K) :
    A.mulVec (r.inverse.mulVec b) = b ↔ ∃ x, A.mulVec x = b := by
  constructor
  · exact fun h => ⟨r.inverse.mulVec b, h⟩
  · rintro ⟨x, rfl⟩
    have h := congrArg (fun M : Matrix (Fin m) (Fin n) K => M.mulVec x)
      (r.mul_inverse_mul A hr)
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h

/-- The zero matrix has the zero generalized inverse, including empty dimensions. -/
theorem NormalizedRref.inverse_zero (r : NormalizedRref K m (n + m))
    (hr : r.Valid (augmentedIdentity (0 : Matrix (Fin m) (Fin n) K))) : r.inverse = 0 := by
  have h := (r.inverse_reflexive 0 hr).outer
  simpa using h.symm

/-- On an invertible square matrix the construction agrees with its usual inverse. -/
theorem NormalizedRref.inverse_eq_of_inverse (A B : Matrix (Fin n) (Fin n) K)
    (r : NormalizedRref K n (n + n)) (hr : r.Valid (augmentedIdentity A))
    (hBA : B * A = 1) (hAB : A * B = 1) : r.inverse = B := by
  calc
    r.inverse = (B * A) * r.inverse * (A * B) := by
      rw [hBA, hAB, Matrix.one_mul, Matrix.mul_one]
    _ = B * (A * r.inverse * A) * B := by simp only [Matrix.mul_assoc]
    _ = B := by rw [r.mul_inverse_mul A hr, hBA, Matrix.one_mul]

end SympyProofs.Rref

namespace SympyProofs.GeneralizedInverse

open SympyProofs.Rref

variable {K : Type*} [Field K] {m n : ℕ}

/-- Reduce the whole augmented matrix once and extract its canonical inverse. -/
def inverseNormalizedRref (rref : NormalizedRrefOperation K) (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin n) (Fin m) K := (rref (augmentedIdentity A)).inverse

/-- A backend-validity theorem yields existence and uniqueness uniformly for all
input matrices; no hypothesis of full rank or squareness is required. -/
theorem inverseNormalizedRref_existsUnique (rref : NormalizedRrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) :
    ∃! G, (rref (augmentedIdentity A)).IsCanonicalInverse A G :=
  (rref (augmentedIdentity A)).existsUnique_canonicalInverse A (valid _)

/-- The prepared inverse is reflexive for any valid RREF backend. -/
theorem inverseNormalizedRref_reflexive (rref : NormalizedRrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) :
    Matrix.IsReflexiveGeneralizedInverse A (inverseNormalizedRref rref A) :=
  (rref (augmentedIdentity A)).inverse_reflexive A (valid _)

theorem inverseNormalizedRref_outer (rref : NormalizedRrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) :
    inverseNormalizedRref rref A * A * inverseNormalizedRref rref A = inverseNormalizedRref rref A :=
  (inverseNormalizedRref_reflexive rref valid A).outer

theorem inverseNormalizedRref_eq (rref₁ rref₂ : NormalizedRrefOperation K)
    (valid₁ : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref₁ A).Valid A)
    (valid₂ : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref₂ A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) : inverseNormalizedRref rref₁ A = inverseNormalizedRref rref₂ A :=
  (rref₁ (augmentedIdentity A)).inverse_eq A (rref₂ (augmentedIdentity A))
    (valid₁ _) (valid₂ _)

end SympyProofs.GeneralizedInverse
