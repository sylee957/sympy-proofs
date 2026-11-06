module

public import SympyProofs.GeneralizedInverse.Algorithm
public import SympyProofs.GeneralizedInverse.Inverse
public import SympyProofs.Rref.Correctness

/-! Correctness and uniqueness of the computed generalized inverse. -/

@[expose] public section

set_option experimental.vcgen true

namespace SympyProofs.GeneralizedInverse

open SympyProofs.Rref

variable {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}

open RrefAlgorithm in
open scoped Std.WP in
/-- The imperative construction agrees with the inverse specified by its RREF certificate. -/
theorem generalizedInverse_eq_certificate (A : Vector (Vector F n) m) :
    toMatrix (generalizedInverse A) =
      let reduced := rref (Vector.ofFn fun i => Vector.ofFn (augmentedIdentity (toMatrix A) i))
      (certificate reduced.rows reduced.pivots).inverse F := by
  let reduced := rref (Vector.ofFn fun i => Vector.ofFn (augmentedIdentity (toMatrix A) i))
  let r := certificate reduced.rows reduced.pivots
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  have hr : r.Valid (augmentedIdentity (toMatrix A)) := h.certificate_valid
  have hmem (p : Fin (n + m)) : p ∈ r.pivots ↔ ∃ i : Fin m, reduced.pivots[i.val] = some p := by
    simp [r, RrefResult.mem_pivots_iff]
  have hzero (j : Fin n) (hj : ¬ ∃ i : Fin m, reduced.pivots[i.val] = some (j.castAdd m)) (k : Fin m) :
      r.inverse F j k = 0 := by
    rw [r.inverse_apply_lookup F, (r.lookup_none_iff _).mpr (fun hp => hj ((hmem _).mp hp))]
  have hentry (i : Fin m) (j : Fin n) (hi : reduced.pivots[i.val] = some (j.castAdd m)) (k : Fin m) :
      r.inverse F j k = reduced.rows[i.val][n + k.val] := by
    rw [r.inverse_apply_lookup F, r.lookup_of_mem hr _ reduced.rows[i.val]
      ((mem_certificate _ _ _ _).mpr ⟨i, hi, rfl⟩)]
    have hone : reduced.rows[i.val][j.val] = 1 := rref_pivot_eq_one _ i (j.castAdd m) hi
    simp [hone]
  have haug : (fun (i : Fin m) (j : Fin (n + m)) =>
      if h : j.val < n then A[i.val][j.val] else if j.val = n + i.val then 1 else 0) =
      augmentedIdentity (toMatrix A) := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun k => ?_) j <;>
      simp [augmentedIdentity, toMatrix, Matrix.one_apply, Fin.ext_iff, eq_comm]
  change toMatrix (generalizedInverse A) = r.inverse F
  generalize he : generalizedInverse A = result
  unfold generalizedInverse at he
  have haugVector := congrArg
    (fun B : Matrix (Fin m) (Fin (n + m)) F => Vector.ofFn fun i => Vector.ofFn (B i)) haug
  rw [haugVector] at he
  apply Std.WP.Id.of_run_eq_wp he
  vcgen (errorOnMissingSpec := false) invariants
  · fun pref _ out => ∀ (j : Fin n) (k : Fin m),
      out[j.val][k.val] =
        if ∃ i ∈ pref, reduced.pivots[i.val] = some (j.castAdd m) then r.inverse F j k else 0
  · fun pref _ values => ∀ k : Fin m,
      values[k.val] = if k ∈ pref then row[n + k.val] else 0
  case vc1 => simp +zetaDelta
  case vc2 =>
    rename_i done hdone
    change (fun i j => done[i.val][j.val]) = r.inverse F
    funext j k
    by_cases hp : ∃ i : Fin m, reduced.pivots[i.val] = some (j.castAdd m)
    · simpa [hp] using hdone j k
    · simpa [hp, hzero j hp k] using hdone j k
  case vc3 =>
    rename_i pref i suff hs before hbefore p hp hright
    change reduced.pivots[i.val] = some p at hp
    intro j k
    have hne : p ≠ j.castAdd m := by
      intro he
      subst p
      exact (Nat.not_le_of_gt j.isLt) hright
    have hmiss : reduced.pivots[i.val] ≠ some (j.castAdd m) := by simpa [hp] using hne
    simpa [List.mem_append, or_and_right, exists_or, hmiss] using hbefore j k
  case vc4 => simp +zetaDelta
  case vc5 =>
    rename_i initialOut pref i suff hs before hbefore p hp hleft done hdone
    change reduced.pivots[i.val] = some p at hp
    have hvalues (k : Fin m) :
        done[k.val] = reduced.rows[i.val][n + k.val] := by
      simpa +zetaDelta using hdone k
    intro j k
    by_cases he : p = j.castAdd m
    · subst p
      simp [out, List.mem_append, or_and_right, exists_or, hp, hvalues, hentry i j hp k]
      rfl
    · have hv : p.val ≠ j.val := fun hv => he (Fin.ext hv)
      have hmiss : reduced.pivots[i.val] ≠ some (j.castAdd m) := by simpa [hp] using he
      simpa [out, Vector.getElem_set, List.mem_append, or_and_right,
        exists_or, hv, hmiss] using hbefore j k
  case vc6 =>
    rename_i pref k suff hs before hbefore
    intro j
    by_cases hkj : k = j
    · subst j
      simp [values]
    · have hv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv)
      simpa [values, Vector.getElem_set, hv, Ne.symm hkj] using hbefore j
  case vc7 =>
    rename_i pref i suff hs before hbefore missing hmissing hp
    have hnone : reduced.pivots[i.val] = none := by
      change reduced.pivots[i.val] = missing at hp
      cases missing <;> simp_all
    intro j k
    simpa [List.mem_append, or_and_right, exists_or, hnone] using hbefore j k

/-- Both reflexive generalized-inverse identities for the computed matrix over `F`. -/
theorem generalizedInverse_reflexive (A : Vector (Vector F n) m) :
    Matrix.IsReflexiveGeneralizedInverse (toMatrix A) (toMatrix (generalizedInverse A)) := by
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  rw [generalizedInverse_eq_certificate]
  simpa using (RrefAlgorithm.certificate _ _).inverse_reflexive F (toMatrix A) h.certificate_valid

/-- The computed inverse has the range prescribed by the input matrix alone. -/
theorem generalizedInverse_range_eq (A : Vector (Vector F n) m) :
    LinearMap.range (toMatrix (generalizedInverse A)).mulVecLin =
      Submodule.pi {j | ∃ x ∈ LinearMap.ker (toMatrix A).mulVecLin,
        IsGreatest (Function.support x) j} (fun _ => ⊥) := by
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  rw [generalizedInverse_eq_certificate]
  simpa using (RrefAlgorithm.certificate _ _).inverse_range_eq F (toMatrix A) h.certificate_valid

/-- The computed inverse has the kernel prescribed by the input matrix alone. -/
theorem generalizedInverse_ker_eq (A : Vector (Vector F n) m) :
    LinearMap.ker (toMatrix (generalizedInverse A)).mulVecLin =
      Submodule.pi {k | ∃ x ∈ LinearMap.range (toMatrix A).mulVecLin,
        IsGreatest (Function.support x) k} (fun _ => ⊥) := by
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  rw [generalizedInverse_eq_certificate]
  simpa using (RrefAlgorithm.certificate _ _).inverse_ker_eq F (toMatrix A) h.certificate_valid

/-- Any reflexive generalized inverse with the computed range and kernel equals
the computed inverse. -/
theorem generalizedInverse_unique_of_range_eq_of_ker_eq
    (A : Vector (Vector F n) m) (G : Matrix (Fin n) (Fin m) F)
    (hG : Matrix.IsReflexiveGeneralizedInverse (toMatrix A) G)
    (hrange : LinearMap.range G.mulVecLin =
      LinearMap.range (toMatrix (generalizedInverse A)).mulVecLin)
    (hker : LinearMap.ker G.mulVecLin =
      LinearMap.ker (toMatrix (generalizedInverse A)).mulVecLin) :
    G = toMatrix (generalizedInverse A) :=
  hG.eq_of_range_eq_of_ker_eq (generalizedInverse_reflexive A) hrange hker

/-- Any implementation returning reflexive generalized inverses with the same
ranges and kernels is equal to `generalizedInverse` as a function. -/
theorem generalizedInverse_algorithm_unique
    (f : Vector (Vector F n) m → Vector (Vector F m) n)
    (hf : ∀ A, Matrix.IsReflexiveGeneralizedInverse (toMatrix A) (toMatrix (f A)))
    (hrange : ∀ A, LinearMap.range (toMatrix (f A)).mulVecLin =
      LinearMap.range (toMatrix (generalizedInverse A)).mulVecLin)
    (hker : ∀ A, LinearMap.ker (toMatrix (f A)).mulVecLin =
      LinearMap.ker (toMatrix (generalizedInverse A)).mulVecLin) :
    f = generalizedInverse := by
  funext A
  have hmatrix := generalizedInverse_unique_of_range_eq_of_ker_eq
    A (toMatrix (f A)) (hf A) (hrange A) (hker A)
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact congrFun (congrFun hmatrix ⟨i, hi⟩) ⟨j, hj⟩

/-- The computed inverse has the canonical pivot supports. -/
theorem generalizedInverse_isCanonical (A : Vector (Vector F n) m) :
    let reduced := rref (Vector.ofFn fun i => Vector.ofFn (augmentedIdentity (toMatrix A) i))
    (RrefAlgorithm.certificate reduced.rows reduced.pivots).IsCanonicalInverse F (toMatrix A)
      (toMatrix (generalizedInverse A)) := by
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  rw [generalizedInverse_eq_certificate]
  exact (RrefAlgorithm.certificate _ _).inverse_isCanonical F (toMatrix A) h.certificate_valid

/-- The support conditions uniquely characterize the computed generalized inverse. -/
theorem generalizedInverse_unique (A : Vector (Vector F n) m) (G : Matrix (Fin n) (Fin m) F)
    (hG : let reduced := rref (Vector.ofFn fun i => Vector.ofFn (augmentedIdentity (toMatrix A) i))
      (RrefAlgorithm.certificate reduced.rows reduced.pivots).IsCanonicalInverse F (toMatrix A) G) :
    G = toMatrix (generalizedInverse A) := by
  have h := rref_valid_ofFn (augmentedIdentity (toMatrix A))
  rw [generalizedInverse_eq_certificate]
  exact hG.eq_inverse F h.certificate_valid

end SympyProofs.GeneralizedInverse

namespace Matrix

variable {F : Type*} [Field F] {m n : ℕ}

open SympyProofs.Rref SympyProofs.GeneralizedInverse in
/-- Every matrix has exactly one reflexive generalized inverse with the prescribed
coordinate range and kernel. Vectors in the inverse's range vanish at the last
nonzero coordinates of vectors in the input's kernel; vectors in the inverse's
kernel vanish at the last nonzero coordinates of vectors in the input's range.
The imperative algorithm supplies the witness. -/
theorem existsUnique_canonicalGeneralizedInverse (A : Matrix (Fin m) (Fin n) F) :
    ∃! G : Matrix (Fin n) (Fin m) F,
      IsReflexiveGeneralizedInverse A G ∧
        (∀ y, y ∈ LinearMap.range G.mulVecLin ↔
          ∀ x ∈ LinearMap.ker A.mulVecLin, ∀ j,
            IsGreatest (Function.support x) j → y j = 0) ∧
        (∀ y, y ∈ LinearMap.ker G.mulVecLin ↔
          ∀ x ∈ LinearMap.range A.mulVecLin, ∀ k,
            IsGreatest (Function.support x) k → y k = 0) := by
  classical
  let input := Vector.ofFn fun i => Vector.ofFn (A i)
  have hview : toMatrix input = A := by
    funext i j
    simp [toMatrix, input]
  let G := toMatrix (generalizedInverse input)
  have hG : IsReflexiveGeneralizedInverse A G := by
    simpa only [hview] using generalizedInverse_reflexive input
  have hrange : LinearMap.range G.mulVecLin =
      Submodule.pi {j | ∃ x ∈ LinearMap.ker A.mulVecLin,
        IsGreatest (Function.support x) j} (fun _ => ⊥) := by
    simpa only [hview] using generalizedInverse_range_eq input
  have hker : LinearMap.ker G.mulVecLin =
      Submodule.pi {k | ∃ x ∈ LinearMap.range A.mulVecLin,
        IsGreatest (Function.support x) k} (fun _ => ⊥) := by
    simpa only [hview] using generalizedInverse_ker_eq input
  refine ⟨G, ⟨hG, ?_, ?_⟩, ?_⟩
  · intro y
    rw [hrange]
    simp only [Submodule.mem_pi, Set.mem_ofPred_eq, Submodule.mem_bot]
    constructor
    · intro h x hx j hj
      exact h j ⟨x, hx, hj⟩
    · rintro h j ⟨x, hx, hj⟩
      exact h x hx j hj
  · intro y
    rw [hker]
    simp only [Submodule.mem_pi, Set.mem_ofPred_eq, Submodule.mem_bot]
    constructor
    · intro h x hx k hk
      exact h k ⟨x, hx, hk⟩
    · rintro h k ⟨x, hx, hk⟩
      exact h x hx k hk
  · intro H hH
    apply hH.1.eq_of_range_eq_of_ker_eq hG
    · apply Submodule.ext
      intro y
      rw [hH.2.1 y, hrange]
      simp only [Submodule.mem_pi, Set.mem_ofPred_eq, Submodule.mem_bot]
      constructor
      · rintro h j ⟨x, hx, hj⟩
        exact h x hx j hj
      · intro h x hx j hj
        exact h j ⟨x, hx, hj⟩
    · apply Submodule.ext
      intro y
      rw [hH.2.2 y, hker]
      simp only [Submodule.mem_pi, Set.mem_ofPred_eq, Submodule.mem_bot]
      constructor
      · rintro h k ⟨x, hx, hk⟩
        exact h x hx k hk
      · intro h x hx k hk
        exact h k ⟨x, hx, hk⟩

end Matrix
