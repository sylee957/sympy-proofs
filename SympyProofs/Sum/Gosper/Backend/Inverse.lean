module

public import SympyProofs.Sum.Gosper.Backend.Rref

/-! A reusable generalized inverse obtained by reducing `[A | I]` once. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] {m n : ℕ}

/-- Augment a matrix by the identity, retaining all possible right-hand sides. -/
def augmentedIdentity (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin m) (Fin (n + m)) K :=
  fun i => Fin.addCases (A i) ((1 : Matrix (Fin m) (Fin m) K) i)

theorem augmentedIdentity_mulVec (A : Matrix (Fin m) (Fin n) K)
    (x : Fin n → K) (b : Fin m → K) :
    (augmentedIdentity A).mulVec (Fin.addCases x (-b)) = A.mulVec x - b := by
  ext i
  simp [augmentedIdentity, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    Matrix.one_apply, sub_eq_add_neg]

/-- Read a solution from row values, setting the free variables to zero. -/
def RrefResult.leftSolution (r : RrefResult K m (n + m)) (b : Fin m → K) :
    Fin n → K := fun j =>
  ∑ i : Fin m, if r.pivots[i.val]? = some (j.castAdd m) then b i / r.denominator else 0

/-- Retain the transformed equations that have no pivot in the coefficient block. -/
def RrefResult.leftResidual (r : RrefResult K m (n + m)) (y : Fin m → K) :
    Fin m → K := fun i =>
  if (r.pivots[i.val]?).any (fun p => decide (p.val < n)) then 0 else y i

/-- The generalized inverse encoded by the right block and the left-block pivots. -/
def RrefResult.inverse (r : RrefResult K m (n + m)) :
    Matrix (Fin n) (Fin m) K := fun j k =>
  ∑ i : Fin m, if r.pivots[i.val]? = some (j.castAdd m) then
    r.matrix i (Fin.natAdd n k) / r.denominator else 0

def RrefResult.leftMatrix (r : RrefResult K m (n + m)) :
    Matrix (Fin m) (Fin n) K := fun i j => r.matrix i (j.castAdd m)

def RrefResult.rightMatrix (r : RrefResult K m (n + m)) :
    Matrix (Fin m) (Fin m) K := fun i k => r.matrix i (Fin.natAdd n k)

theorem RrefResult.mulVec_addCases (r : RrefResult K m (n + m))
    (x : Fin n → K) (b : Fin m → K) :
    r.matrix.mulVec (Fin.addCases x (-b)) =
      r.leftMatrix.mulVec x - r.rightMatrix.mulVec b := by
  ext i
  simp [leftMatrix, rightMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]

theorem RrefResult.inverse_mulVec (r : RrefResult K m (n + m)) (b : Fin m → K) :
    r.inverse.mulVec b =
      r.leftSolution (r.rightMatrix.mulVec b) := by
  ext j
  simp only [inverse, leftSolution, rightMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : r.pivots[i.val]? = some (j.castAdd m)
  · simp [hp, Finset.sum_div, div_mul_eq_mul_div]
  · simp [hp]

/-- Reconstructing the left-pivot variables satisfies exactly the left-pivot rows. -/
theorem RrefResult.leftSolution_mulVec_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (y : Fin m → K) :
    r.leftMatrix.mulVec (r.leftSolution y) = y - r.leftResidual y := by
  ext i
  simp only [leftMatrix, Matrix.mulVec, dotProduct, leftSolution, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin m, if i = k then y k - r.leftResidual y k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      cases hp : r.pivots[k.val]? with
      | none => simp [leftResidual, hp]
      | some p =>
        revert hp
        refine Fin.addCases (fun j hp => ?_) (fun j hp => ?_) p
        · simp only [Option.some.injEq, Fin.castAdd_inj]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rw [hr.pivot_column k (j.castAdd m) hp i]
          simp only [leftResidual, hp, Option.any_some, Fin.val_castAdd,
            j.isLt, decide_true, ↓reduceIte, sub_zero]
          split_ifs
          · field_simp [hr.denominator_ne_zero]
          · simp
        · have hne (x : Fin n) : Fin.natAdd n j ≠ x.castAdd m := by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
            omega
          simp [leftResidual, hp, hne]
    _ = _ := by simp

/-- The unsatisfied transformed rows detect consistency without multiplying the
coefficient vector by the original matrix again. -/
theorem RrefResult.leftResidual_eq_zero_iff (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A))
    (rhs : Fin m → K) :
    r.leftResidual (r.rightMatrix.mulVec rhs) = 0 ↔
      A.mulVec (r.inverse.mulVec rhs) = rhs := by
  have hk := hr.kernel_iff (Fin.addCases (r.inverse.mulVec rhs) (-rhs))
  rw [augmentedIdentity_mulVec, sub_eq_zero, mulVec_addCases, inverse_mulVec,
    leftSolution_mulVec_eq r hr] at hk
  simpa only [inverse_mulVec, sub_sub_cancel_left, neg_eq_zero] using hk.symm

theorem RrefResult.leftSolution_mulVec (A : Matrix (Fin m) (Fin n) K)
    (r : RrefResult K m (n + m)) (hr : r.Valid (augmentedIdentity A))
    (x : Fin n → K) :
    r.leftMatrix.mulVec (r.leftSolution (r.leftMatrix.mulVec x)) =
      r.leftMatrix.mulVec x := by
  let v : Fin m → K := r.leftMatrix.mulVec x
  have he : ∀ i : Fin m,
      ∑ j : Fin n, r.matrix i (j.castAdd m) * r.leftSolution v j = v i := by
    intro i
    simp only [leftSolution, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ k : Fin m, if i = k then v k else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        cases hp : r.pivots[k.val]? with
        | none =>
          have hv : v k = 0 := by
            simp [v, leftMatrix, Matrix.mulVec, dotProduct, hr.zero_row k hp]
          simp [hv]
        | some p =>
          revert hp
          refine Fin.addCases (fun j hp => ?_) (fun j hp => ?_) p
          · simp only [Option.some.injEq, Fin.castAdd_inj]
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
            rw [hr.pivot_column k (j.castAdd m) hp i]
            split_ifs
            · field_simp [hr.denominator_ne_zero]
            · simp
          · have hv : v k = 0 := by
              have hz : ∀ l : Fin n, r.matrix k (l.castAdd m) = 0 := by
                intro l
                apply hr.before_pivot k (Fin.natAdd n j) hp
                simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
                omega
              simp [v, leftMatrix, Matrix.mulVec, dotProduct, hz]
            simp [hv]
      _ = _ := by simp
  exact funext he

/-- Compute RREF once on `[A | I]`, then retain its generalized inverse. -/
def inverseRref (rref : RrefOperation K) (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin n) (Fin m) K := Id.run do
  let r := rref (augmentedIdentity A)
  return r.inverse

/-- The prepared inverse recovers a preimage for every vector in the image of `A`. -/
theorem inverseRref_mulVec (rref : RrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    A.mulVec ((inverseRref rref A).mulVec (A.mulVec x)) = A.mulVec x := by
  let r := rref (augmentedIdentity A)
  have hr : r.Valid (augmentedIdentity A) := valid _
  have he : r.leftMatrix.mulVec x = r.rightMatrix.mulVec (A.mulVec x) := by
    have hk := (hr.kernel_iff (Fin.addCases x (-A.mulVec x))).mp
      (by rw [augmentedIdentity_mulVec, sub_self])
    rwa [RrefResult.mulVec_addCases, sub_eq_zero] at hk
  have hk : r.matrix.mulVec (Fin.addCases (r.inverse.mulVec (A.mulVec x))
      (-A.mulVec x)) = 0 := by
    rw [RrefResult.mulVec_addCases, RrefResult.inverse_mulVec, ← he,
      RrefResult.leftSolution_mulVec A r hr, sub_self]
  have ha := (hr.kernel_iff _).mpr hk
  rw [augmentedIdentity_mulVec, sub_eq_zero] at ha
  exact ha

/-- The matrix prepared from `[A | I]` satisfies the generalized-inverse identity. -/
theorem inverseRref_mul (rref : RrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) :
    A * inverseRref rref A * A = A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using inverseRref_mulVec rref valid A x

/-- Solving a new right-hand side only needs multiplication by the prepared inverse
and a consistency check against the original matrix. -/
theorem inverseRref_solve_iff (rref : RrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    A.mulVec ((inverseRref rref A).mulVec b) = b ↔ ∃ x, A.mulVec x = b := by
  constructor
  · intro h
    exact ⟨(inverseRref rref A).mulVec b, h⟩
  · rintro ⟨x, rfl⟩
    exact inverseRref_mulVec rref valid A x

theorem inverseRref_residual_eq_zero_iff (rref : RrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    A.mulVec ((inverseRref rref A).mulVec b) - b = 0 ↔ ∃ x, A.mulVec x = b := by
  rw [sub_eq_zero, inverseRref_solve_iff rref valid A b]

end Gosper.Algorithm
