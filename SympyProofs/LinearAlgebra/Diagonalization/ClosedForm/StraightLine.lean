module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Interpolation
public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite diagonalization by principal radicals

The lengths of the root list and the column assignments fix the number of operations.
The scalar reciprocal has a nonzero denominator for every complex input.
-/

@[expose] public section

noncomputable section

namespace SympyProofs.Diagonalization.StraightLine

open Complex Matrix Polynomial Lagrange

/-- The fourth root puts every nonzero input in the open right half-plane.
At zero, the final square root takes its value on the negative real axis. -/
def zeroIndicator (z : ℂ) : ℂ :=
  let a := z.sqrt.sqrt - I
  ((a ^ 2).sqrt - a) / (2 * I)

theorem zeroIndicator_eq (z : ℂ) : zeroIndicator z = if z = 0 then 1 else 0 := by
  by_cases hz : z = 0
  · subst z
    simp [zeroIndicator, Complex.sqrt_neg_one, ← two_mul]
  · have hsquare : z.sqrt ^ 2 = z := Complex.cpow_nat_inv_pow z (by decide)
    have hs : z.sqrt ≠ 0 := fun h => hz (by simpa [h] using hsquare.symm)
    have hr : 0 ≤ z.sqrt.re := by rw [Complex.sqrt, cpow_inv_two_re]; positivity
    have hp : 0 < z.sqrt.sqrt.re := by
      rw [Complex.sqrt, cpow_inv_two_re]
      exact Real.sqrt_pos.mpr (half_pos (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hs) hr))
    have ha : 0 < (z.sqrt.sqrt - I).re := by simpa using hp
    have hsq : ((z.sqrt.sqrt - I) ^ 2).sqrt = z.sqrt.sqrt - I := Complex.sq_cpow_two_inv ha
    simp [zeroIndicator, hsq, hz]

/-- Reciprocal with value zero at zero and an everywhere nonzero denominator. -/
def reciprocal (z : ℂ) : ℂ := (1 - zeroIndicator z) / (z + zeroIndicator z)

theorem denominator_ne_zero (z : ℂ) : z + zeroIndicator z ≠ 0 := by
  by_cases hz : z = 0 <;> simp [zeroIndicator_eq, hz]

theorem reciprocal_eq (z : ℂ) : reciprocal z = z⁻¹ := by
  by_cases hz : z = 0 <;> simp [reciprocal, zeroIndicator_eq, hz]

section Interpolation

variable {n : ℕ} {K : Type*} [Field K] (Z R : K → K) [DecidableEq K]
variable (hZ : ∀ z, Z z = if z = 0 then 1 else 0) (hR : ∀ z, R z = z⁻¹)

/-- Product over the fixed list, with a factor of zero for every match. -/
def absent (x : K) (xs : List K) : K :=
  (xs.map fun y => 1 - Z (x - y)).prod

include hZ in
private theorem absent_eq (x : K) (xs : List K) :
    absent Z x xs = if x ∈ xs then 0 else 1 := by
  induction xs with
  | nil => simp [absent]
  | cons y ys ih =>
    change (1 - Z (x - y)) * absent Z x ys = _
    by_cases h : x = y <;> simp [hZ, sub_eq_zero, h, ih]

/-- Multiply one factor per distinct root outside the excluded list. A repeated
or excluded factor contributes the identity matrix. -/
def factorProduct (factor : K → Matrix (Fin n) (Fin n) K) (excluded : List K) :
    List K → Matrix (Fin n) (Fin n) K
  | [] => 1
  | x :: xs =>
    (1 + absent Z x (excluded ++ xs) • (factor x - 1)) * factorProduct factor excluded xs

include hZ in
private theorem factorProduct_eval (A : Matrix (Fin n) (Fin n) K)
    (f : K → K[X]) (excluded xs : List K) :
    factorProduct Z (fun x => aeval A (f x)) excluded xs =
      aeval A (∏ x ∈ xs.toFinset \ excluded.toFinset, f x) := by
  induction xs with
  | nil => simp [factorProduct]
  | cons x xs ih =>
    simp only [factorProduct, ih, absent_eq Z hZ, List.mem_append, List.toFinset_cons]
    by_cases he : x ∈ excluded
    · simp [he, Finset.insert_sdiff_of_mem _ (List.mem_toFinset.mpr he)]
    · by_cases hx : x ∈ xs
      · simp [hx, Finset.insert_eq_of_mem (List.mem_toFinset.mpr hx)]
      · have hnot : x ∉ excluded.toFinset := by simpa using he
        simp [hx, he, Finset.insert_sdiff_of_notMem _ hnot, Finset.prod_insert,
          show x ∉ xs.toFinset \ excluded.toFinset by simp [hx]]

/-- The normalized product for the eigenspace belonging to μ. -/
def projector (A : Matrix (Fin n) (Fin n) K) (xs : List K) (μ : K) : Matrix (Fin n) (Fin n) K :=
  factorProduct Z (fun x => R (μ - x) • (A - x • 1)) [μ] xs

include hZ hR in
private theorem projector_eq (A : Matrix (Fin n) (Fin n) K) (xs : List K) (μ : K) :
    projector Z R A xs μ = aeval A (Lagrange.basis xs.toFinset id μ) := by
  have h (x : K) : R (μ - x) • (A - x • 1) = aeval A (basisDivisor μ x) := by
    simp [hR, basisDivisor, Algebra.algebraMap_eq_smul_one]
  simp [projector, h, factorProduct_eval Z hZ, Finset.sdiff_singleton_eq_erase, Lagrange.basis]

/-- Each candidate takes its j-th column from the projector for the j-th root label. -/
def candidate (A : Matrix (Fin n) (Fin n) K) (xs : List K) (d : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  of fun i j => projector Z R A xs (d j) i j

include hZ hR in
private theorem candidate_eq (A : Matrix (Fin n) (Fin n) K) (xs : List K) (d : Fin n → K) :
    candidate Z R A xs d = basisCandidate A xs d := by
  simp [candidate, projector_eq Z R hZ hR, basisCandidate]

/-- A weighted sum over the fixed candidate list. The first invertible basis
has coefficient one and every other basis has coefficient zero. -/
def selectBasis (A : Matrix (Fin n) (Fin n) K) (xs : List K) :
    List (Fin n → K) → Matrix (Fin n) (Fin n) K × (Fin n → K)
  | [] => 0
  | d :: ds =>
    let P := candidate Z R A xs d
    let z := Z P.det
    (1 - z) • (P, d) + z • selectBasis A xs ds

include hZ hR in
private theorem selectBasis_eq (A : Matrix (Fin n) (Fin n) K)
    (xs : List K) (ds : List (Fin n → K)) :
    selectBasis Z R A xs ds =
      ((ds.find? fun d => (basisCandidate A xs d).det ≠ 0).map
        fun d => (basisCandidate A xs d, d)).getD 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hd : (basisCandidate A xs d).det = 0 <;>
      simp [selectBasis, candidate_eq Z R hZ hR, hZ, hd, ih]

/-- One exactly when every entry vanishes. -/
def zeroMatrixIndicator (M : Matrix (Fin n) (Fin n) K) : K := ∏ i, ∏ j, Z (M i j)

include hZ in
private theorem zeroMatrixIndicator_eq (M : Matrix (Fin n) (Fin n) K) :
    zeroMatrixIndicator Z M = if M = 0 then 1 else 0 := by
  simp only [zeroMatrixIndicator, hZ, Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

/-- Assemble a basis from a fixed list of root labels. -/
def fromRoots (A : Matrix (Fin n) (Fin n) K) (xs : List K) :
    Matrix (Fin n) (Fin n) K × (Fin n → K) :=
  let N := factorProduct Z (fun x => A - x • 1) [] xs
  zeroMatrixIndicator Z N • selectBasis Z R A xs (assignments xs n)

include hZ hR in
theorem fromRoots_eq (A : Matrix (Fin n) (Fin n) K) (xs : List K) :
    fromRoots Z R A xs = (diagonalizeWith A xs).getD 0 := by
  have h (x : K) : A - x • 1 = aeval A (X - C x) := by
    simp [Algebra.algebraMap_eq_smul_one]
  simp only [fromRoots, h, factorProduct_eval Z hZ, List.toFinset_nil, Finset.sdiff_empty,
    zeroMatrixIndicator_eq Z hZ, selectBasis_eq Z R hZ hR]
  unfold diagonalizeWith distinctFactorProduct nodal
  split <;> simp_all

end Interpolation

variable {n : ℕ}

/-- Every real eigenvalue occurs among the real parts of the complex labels. -/
theorem realLabels_cover (A : Matrix (Fin n) (Fin n) ℝ) {xs : List ℂ}
    (cover : ∀ z, (A.map ofRealHom).charpoly.eval z = 0 → z ∈ xs)
    (x : ℝ) (hx : A.charpoly.eval x = 0) : x ∈ xs.map Complex.re := by
  apply List.mem_map.mpr
  refine ⟨(x : ℂ), cover _ ?_, rfl⟩
  rw [charpoly_map]
  change (A.charpoly.map ofRealHom).eval (ofRealHom x) = 0
  rw [eval_map_apply, hx, map_zero]

/-- A basis and diagonal over ℂ, or the zero pair when no basis exists. -/
def complexFromRoots (A : Matrix (Fin n) (Fin n) ℂ) (xs : List ℂ) :=
  fromRoots zeroIndicator reciprocal A xs

theorem complexFromRoots_eq (A : Matrix (Fin n) (Fin n) ℂ) (xs : List ℂ) :
    complexFromRoots A xs = (diagonalizeWith A xs).getD 0 :=
  fromRoots_eq _ _ zeroIndicator_eq reciprocal_eq A xs

/-- A basis over ℝ using the real parts of the complex radical expressions as labels. -/
def realFromRoots (A : Matrix (Fin n) (Fin n) ℝ) (xs : List ℂ) :=
  fromRoots (fun x : ℝ => (zeroIndicator x).re) (fun x : ℝ => (reciprocal x).re) A
    (xs.map Complex.re)

theorem realFromRoots_eq (A : Matrix (Fin n) (Fin n) ℝ) (xs : List ℂ) :
    realFromRoots A xs = (diagonalizeWith A (xs.map Complex.re)).getD 0 := by
  apply fromRoots_eq
  · intro x
    by_cases h : x = 0 <;> simp [zeroIndicator_eq, h]
  · intro x
    simp [reciprocal_eq, ← Complex.ofReal_inv]

variable {K : Type*} [Field K] [DecidableEq K]

theorem getD_correct [NeZero n] (A : Matrix (Fin n) (Fin n) K) {xs : List K}
    (cover : ∀ x, A.charpoly.eval x = 0 → x ∈ xs) (h : ∃ P d, IsDiagonalization A P d) :
    let result := (diagonalizeWith A xs).getD 0
    IsDiagonalization A result.1 result.2 := by
  obtain ⟨⟨P, d⟩, hd⟩ := Option.isSome_iff_exists.mp ((diagonalizeWith_isSome_iff A cover).mpr h)
  simpa [hd] using diagonalizeWith_sound hd

theorem getD_eq_zero_of_no_basis (A : Matrix (Fin n) (Fin n) K)
    (xs : List K) (h : ¬ ∃ P d, IsDiagonalization A P d) :
    (diagonalizeWith A xs).getD 0 = 0 := by
  cases hd : diagonalizeWith A xs with
  | none => rfl
  | some pair => exact (h ⟨pair.1, pair.2, diagonalizeWith_sound hd⟩).elim

end SympyProofs.Diagonalization.StraightLine
