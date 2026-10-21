module

public import SympyProofs.Gosper.Algorithm.Polynomial

/-! Contracts for the matrix/denominator/pivots returned by `DomainMatrix.rref_den`.
The contract describes the result, independently of dense or sparse storage and
of whether a backend mutates a private working matrix. Ordinary RREF uses
denominator one. No correctness of SymPy's Python implementation is assumed. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] {m n : ℕ}

structure RrefResult (K : Type*) (m n : ℕ) where
  matrix : Matrix (Fin m) (Fin n) K
  denominator : K
  pivots : List (Fin n)
  /-- Each pivot corresponds to a row of the matrix. -/
  length_le : pivots.length ≤ m

/-- The numerator matrix is a nonzero scalar multiple of RREF. The pivot list
enumerates the leading columns of the nonzero rows, in row order. Equality of
kernels is the row-equivalence property needed for an augmented system. -/
structure RrefResult.Valid (A : Matrix (Fin m) (Fin n) K) (r : RrefResult K m n) : Prop where
  denominator_ne_zero : r.denominator ≠ 0
  ordered : r.pivots.Pairwise (· < ·)
  pivot_column : ∀ (i : Fin m) (j : Fin n), r.pivots[i.val]? = some j →
    ∀ k : Fin m, r.matrix k j = if k = i then r.denominator else 0
  before_pivot : ∀ (i : Fin m) (j : Fin n), r.pivots[i.val]? = some j →
    ∀ k < j, r.matrix i k = 0
  zero_row : ∀ i : Fin m, r.pivots[i.val]? = none → r.matrix i = 0
  kernel_iff : ∀ x : Fin n → K, A.mulVec x = 0 ↔ r.matrix.mulVec x = 0

/-- The matrix primitive returns a pivot list with its structural row bound.
Its algebraic correctness contract is separate from the operation. -/
abbrev RrefOperation (K : Type*) :=
  {m n : ℕ} → Matrix (Fin m) (Fin n) K → RrefResult K m n

def augmented (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    Matrix (Fin m) (Fin (n + 1)) K := fun i => Fin.snoc (A i) (b i)

theorem augmented_mulVec (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (x : Fin n → K) :
    (augmented A b).mulVec (Fin.snoc x (-1)) = A.mulVec x - b := by
  ext i
  simp [augmented, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, sub_eq_add_neg]

/-- Mathematical specification of a particular solution; all free variables are zero. -/
def RrefResult.solution (r : RrefResult K m (n + 1)) : Fin n → K := fun j =>
  ∑ i : Fin m, if r.pivots[i.val]? = some j.castSucc then
    r.matrix i (Fin.last n) / r.denominator else 0

/-- The solution polynomial is obtained by adding one monomial for each pivot row. -/
theorem RrefResult.ofFn_solution_eq [DecidableEq K] (r : RrefResult K m (n + 1))
    (hlast : Fin.last n ∉ r.pivots) :
    Polynomial.ofFn n r.solution =
      ∑ i : Fin m, (r.pivots[i.val]?).elim 0
        (fun pivot => Polynomial.monomial (pivot : ℕ) (r.matrix i (Fin.last n) / r.denominator)) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [solution, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : r.pivots[i.val]? with
  | none => simp
  | some pivot =>
    have hpne : pivot ≠ Fin.last n := by
      intro he
      exact hlast (he ▸ List.mem_of_getElem? hp)
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hpne
    simp [apply_ite]

/-- Reconstructing the solution only requires the enumerated pivot rows. -/
theorem RrefResult.ofFn_solution_eq_pivots [DecidableEq K]
    (r : RrefResult K m (n + 1)) (hlast : Fin.last n ∉ r.pivots) :
    Polynomial.ofFn n r.solution =
      (r.pivots.mapFinIdx fun i pivot hi =>
        Polynomial.monomial (pivot : ℕ)
          (r.matrix ⟨i, lt_of_lt_of_le hi r.length_le⟩ (Fin.last n) / r.denominator)).sum := by
  rw [r.ofFn_solution_eq hlast, List.mapFinIdx_eq_ofFn, List.sum_ofFn]
  symm
  apply Fintype.sum_of_injective (Fin.castLE r.length_le) (Fin.castLE_injective _)
  · intro i hi
    have houtside : ¬i.val < r.pivots.length := by
      intro hlt
      exact hi ⟨⟨i.val, hlt⟩, rfl⟩
    simp [houtside]
  · intro i
    simp [i.isLt, Fin.castLE]

theorem RrefResult.solution_correct (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (r : RrefResult K m (n + 1)) (hr : r.Valid (augmented A b))
    (hlast : Fin.last n ∉ r.pivots) : A.mulVec r.solution = b := by
  have he : ∀ i : Fin m,
      ∑ j : Fin n, r.matrix i j.castSucc * r.solution j = r.matrix i (Fin.last n) := by
    intro i
    simp only [solution, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ k : Fin m, if i = k then r.matrix k (Fin.last n) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        cases hp : r.pivots[k.val]? with
        | none =>
          have hz := congrFun (hr.zero_row k hp) (Fin.last n)
          simp [hz]
        | some p =>
          have hpne : p ≠ Fin.last n := by
            intro h
            exact hlast (h ▸ List.mem_of_getElem? hp)
          obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hpne
          simp only [Option.some.injEq, Fin.castSucc_inj]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rw [hr.pivot_column k j.castSucc hp i]
          split_ifs
          · field_simp [hr.denominator_ne_zero]
          · simp
      _ = _ := by simp
  have hk : r.matrix.mulVec (Fin.snoc r.solution (-1)) = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, mul_neg, mul_one, Pi.zero_apply]
    rw [he i]
    exact add_neg_cancel _
  have ha := (hr.kernel_iff _).mpr hk
  rw [augmented_mulVec, sub_eq_zero] at ha
  exact ha

theorem RrefResult.inconsistent (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (r : RrefResult K m (n + 1)) (hr : r.Valid (augmented A b))
    (hlast : Fin.last n ∈ r.pivots) : ¬∃ x, A.mulVec x = b := by
  obtain ⟨i, hi, hp⟩ := List.getElem_of_mem hlast
  let k : Fin m := ⟨i, lt_of_lt_of_le hi r.length_le⟩
  have hk : r.pivots[k.val]? = some (Fin.last n) := by simp [k, hi, hp]
  rintro ⟨x, hx⟩
  have he := congrFun ((hr.kernel_iff (Fin.snoc x (-1))).mp
    (by rw [augmented_mulVec, hx, sub_self])) k
  have hz : ∀ j : Fin n, r.matrix k j.castSucc = 0 :=
    fun j => hr.before_pivot k (Fin.last n) hk _ (Fin.castSucc_lt_last j)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz,
    hr.pivot_column k (Fin.last n) hk k] at he
  exact hr.denominator_ne_zero he

/-- SymPy-style augmented RREF solve: a pivot in the right-hand-side column
means inconsistency; otherwise read pivot variables and set free variables to zero. -/
def solveRref (rref : RrefOperation K) (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) : Option (Fin n → K) := Id.run do
  let r := rref (augmented A b)
  if Fin.last n ∈ r.pivots then return none
  return some r.solution

theorem solveRref_spec (rref : RrefOperation K)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    match solveRref rref A b with
    | some x => A.mulVec x = b
    | none => ¬∃ x, A.mulVec x = b := by
  dsimp [solveRref]
  split_ifs with h
  · exact RrefResult.inconsistent A b _ (valid _) h
  · exact RrefResult.solution_correct A b _ (valid _) h

end Gosper.Algorithm
