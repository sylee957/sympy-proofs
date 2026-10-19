import SympyProofs.MoorePenrose.Faddeev.Denominator
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Order.Interval.Finset.Fin

/-!
# Singular-value characterization and the exact rank-drop locus

`singularValues A` lists the square roots of the eigenvalues of `Aᴴ * A`,
indexed by the column type. This pads the usual list with zeros for a wide
matrix. The formulas are symmetric and do not require a choice of ordering.
`orderedSingularValues A` additionally lists them in decreasing order.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix Polynomial
open scoped ComplexOrder

section Elementary

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem elementary_nonneg (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (k : ℕ) :
    0 ≤ elementary d k :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => hd i

omit [DecidableEq n] in
/-- A nonnegative elementary symmetric function is positive exactly when there
are at least `k` nonzero arguments. -/
theorem elementary_pos_iff (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (k : ℕ) :
    0 < elementary d k ↔ k ≤ Fintype.card {i // d i ≠ 0} := by
  classical
  rw [elementary, Finset.sum_pos_iff_of_nonneg
    (fun s _ => Finset.prod_nonneg fun i _ => hd i)]
  have hc : Fintype.card {i // d i ≠ 0} =
      (Finset.univ.filter fun i => d i ≠ 0).card := by simp [Fintype.card_subtype]
  rw [hc]
  constructor
  · rintro ⟨s, hs, hp⟩
    have hsub : s ⊆ Finset.univ.filter (fun i => d i ≠ 0) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.prod_ne_zero_iff.mp (ne_of_gt hp)) i hi
    simpa only [(Finset.mem_powersetCard.mp hs).2] using Finset.card_le_card hsub
  · intro hk
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hk
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    exact Finset.prod_pos fun i hi => lt_of_le_of_ne (hd i)
      (Ne.symm (Finset.mem_filter.mp (hs hi)).2)

omit [DecidableEq n] in
theorem spectralPolynomial_top_eq_prod {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (d : n → K) :
    (spectralPolynomial d Finset.univ).coeff (Fintype.card {i // d i ≠ 0}) =
      ∏ i ∈ Finset.univ.filter (fun i => d i ≠ 0), d i := by
  rw [← spectralPolynomial_natDegree d]
  change (spectralPolynomial d Finset.univ).leadingCoeff = _
  rw [spectralPolynomial, Polynomial.leadingCoeff_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : d i = 0
  · simp [hi]
  · simpa [hi, add_comm] using (Polynomial.leadingCoeff_linear (b := (1 : K)) hi)

end Elementary

section SingularValues

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- Singular values, indexed by the columns and padded with zeros if necessary. -/
noncomputable def singularValues (A : Matrix m n 𝕜) (i : n) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

theorem singularValues_nonneg (A : Matrix m n 𝕜) (i : n) : 0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

theorem singularValues_sq (A : Matrix m n 𝕜) (i : n) :
    singularValues A i ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

theorem rank_eq_card_nonzero_singularValues (A : Matrix m n 𝕜) :
    A.rank = Fintype.card {i // singularValues A i ≠ 0} := by
  classical
  rw [← Matrix.rank_conjTranspose_mul_self A,
    (Matrix.isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs]
  simp only [← singularValues_sq, ne_eq, pow_eq_zero_iff (by decide : 2 ≠ 0)]

/-- Singular values in decreasing order, indexed from zero and padded to the
number of columns. -/
noncomputable def orderedSingularValues (A : Matrix m n 𝕜)
    (i : Fin (Fintype.card n)) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ i)

theorem orderedSingularValues_nonneg (A : Matrix m n 𝕜)
    (i : Fin (Fintype.card n)) : 0 ≤ orderedSingularValues A i :=
  Real.sqrt_nonneg _

theorem orderedSingularValues_antitone (A : Matrix m n 𝕜) :
    Antitone (orderedSingularValues A) :=
  fun _ _ hij => Real.sqrt_le_sqrt
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_antitone hij)

theorem singularValues_eq_orderedSingularValues (A : Matrix m n 𝕜) (i : n) :
    singularValues A i = orderedSingularValues A
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := rfl

theorem rank_eq_card_nonzero_orderedSingularValues (A : Matrix m n 𝕜) :
    A.rank = Fintype.card {i // orderedSingularValues A i ≠ 0} := by
  classical
  rw [rank_eq_card_nonzero_singularValues]
  exact Fintype.card_congr ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm.subtypeEquiv
    (fun i => by rw [singularValues_eq_orderedSingularValues]))

/-- The zero entries of the decreasing singular-value list start exactly at the rank. -/
theorem orderedSingularValues_eq_zero_iff (A : Matrix m n 𝕜)
    (i : Fin (Fintype.card n)) :
    orderedSingularValues A i = 0 ↔ A.rank ≤ i.val := by
  classical
  have hc : A.rank = (Finset.univ.filter
      (fun j => orderedSingularValues A j ≠ 0)).card := by
    rw [rank_eq_card_nonzero_orderedSingularValues, Fintype.card_subtype]
  rw [hc]
  constructor
  · intro hi
    have hsub : Finset.univ.filter (fun j => orderedSingularValues A j ≠ 0) ⊆
        Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hle := orderedSingularValues_antitone A (le_of_not_gt hji)
      rw [hi] at hle
      exact (Finset.mem_filter.mp hj).2
        (le_antisymm hle (orderedSingularValues_nonneg A j))
    simpa only [Fin.card_Iio] using Finset.card_le_card hsub
  · intro hr
    by_contra hi
    have hp : 0 < orderedSingularValues A i :=
      lt_of_le_of_ne (orderedSingularValues_nonneg A i) (Ne.symm hi)
    have hsub : Finset.Iic i ⊆
        Finset.univ.filter (fun j => orderedSingularValues A j ≠ 0) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ne_of_gt (lt_of_lt_of_le hp
        (orderedSingularValues_antitone A (Finset.mem_Iic.mp hj)))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

/-- Every denominator coefficient is the elementary symmetric function of the
squared singular values. This holds for every `k`, not only the actual rank. -/
theorem denominator_eq_elementary_singularValues (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k = ((elementary (fun i => singularValues A i ^ 2) k : ℝ) : 𝕜) := by
  have h := congrArg Prod.fst
    (state_spectral (Matrix.isHermitian_conjTranspose_mul_self A) k)
  change denominator A k = _ at h
  rw [h, spectralPolynomial_coeff_eq_elementary]
  simp [elementary, singularValues_sq]

/-- At the actual rank, the denominator is the product of the nonzero squared
singular values. The empty product is one, including for the zero matrix. -/
theorem denominator_rank_eq_prod_singularValues (A : Matrix m n 𝕜) :
    denominator A A.rank =
      ((∏ i ∈ Finset.univ.filter (fun i => singularValues A i ≠ 0),
        singularValues A i ^ 2 : ℝ) : 𝕜) := by
  classical
  rw [denominator_eq_elementary_singularValues,
    ← spectralPolynomial_coeff_eq_elementary, rank_eq_card_nonzero_singularValues]
  have hc : Fintype.card {i // singularValues A i ≠ 0} =
      Fintype.card {i // singularValues A i ^ 2 ≠ 0} := by simp
  rw [hc, spectralPolynomial_top_eq_prod]
  simp

/-- Positivity of the real denominator is exactly a rank lower bound. -/
theorem denominator_re_pos_iff (A : Matrix m n 𝕜) (k : ℕ) :
    0 < RCLike.re (denominator A k) ↔ k ≤ A.rank := by
  rw [denominator_eq_elementary_singularValues, RCLike.ofReal_re,
    elementary_pos_iff _ (fun i => sq_nonneg _) k, rank_eq_card_nonzero_singularValues]
  simp

/-- The complete zero-locus theorem, including `k = 0` and `k` beyond the dimensions. -/
theorem denominator_eq_zero_iff_rank_lt (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k = 0 ↔ A.rank < k := by
  constructor
  · intro hz
    by_contra hr
    have hp := (denominator_re_pos_iff A k).mpr (Nat.le_of_not_gt hr)
    simp [hz] at hp
  · exact denominator_eq_zero_of_rank_lt A

theorem denominator_ne_zero_iff_le_rank (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k ≠ 0 ↔ k ≤ A.rank := by
  rw [ne_eq, denominator_eq_zero_iff_rank_lt, not_lt]

/-- Equivalently, the `k`-th denominator vanishes exactly when the `k`-th largest
singular value vanishes (the Lean singular-value index is zero-based). -/
theorem denominator_eq_zero_iff_orderedSingularValues_eq_zero (A : Matrix m n 𝕜)
    (i : Fin (Fintype.card n)) :
    denominator A (i.val + 1) = 0 ↔ orderedSingularValues A i = 0 := by
  rw [denominator_eq_zero_iff_rank_lt, orderedSingularValues_eq_zero_iff]
  omega

/-- On a family of maximal rank `r`, the fixed denominator is nonzero exactly
where rank `r` is preserved. -/
theorem denominator_ne_zero_iff_rank_eq (A : Matrix m n 𝕜) (r : ℕ) (hr : A.rank ≤ r) :
    denominator A r ≠ 0 ↔ A.rank = r := by
  rw [denominator_ne_zero_iff_le_rank]
  exact ⟨fun h => Nat.le_antisymm hr h, fun h => h ▸ le_refl r⟩

/-- The zero set of the symbolically computed denominator is exactly the rank-drop
set after any specialization preserving conjugation. The index `r` stays fixed. -/
theorem specialization_denominator_eq_zero_iff
    {R : Type*} [CommRing R] [Algebra ℚ R] [StarRing R]
    (f : R →ₐ[ℚ] 𝕜) (hf : ∀ x, f (star x) = star (f x))
    (A : Matrix m n R) (r : ℕ) :
    f (denominator A r) = 0 ↔ (A.map f).rank < r := by
  rw [← denominator_map f hf]
  exact denominator_eq_zero_iff_rank_lt _ _

end SingularValues

section SubmatrixDeterminants

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]

/-- The submatrix determinant and spectral characterizations give the same rank-drop locus. -/
theorem rank_lt_iff_all_submatrix_det_zero (A : Matrix m n 𝕜) (k : ℕ) :
    A.rank < k ↔
      ∀ (rows : Fin k ↪o m) (cols : Fin k ↪o n),
        (A.submatrix rows cols).det = 0 := by
  rw [← denominator_eq_zero_iff_rank_lt, denominator_eq_zero_iff_all_submatrix_det_zero]

end SubmatrixDeterminants

end SympyProofs.MoorePenrose.Faddeev
