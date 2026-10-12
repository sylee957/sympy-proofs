import SympyProofs.JordanKrylov.MinimalAnnihilatingPolynomial

/-!
# Constructing a vector's minimal polynomial from a Krylov relation

The first dependence `A^r u = ∑ i < r, cᵢ • A^i u` gives the polynomial
`X^r - ∑ i < r, cᵢ X^i`. The constructor takes explicit coefficients;
it does not choose a generator of an ideal or solve a linear system.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix
open scoped BigOperators

/-- The `j`th Krylov vector: `u, Au, A²u, …`. -/
def krylovVector {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (j : ℕ) : Fin n → K :=
  (A ^ j) *ᵥ u

/-- Construct the monic polynomial from `A^r u = ∑ i < r, cᵢ • A^i u`. -/
noncomputable def krylovPolynomial {K : Type*} [Field K] {r : ℕ} (c : Fin r → K) : K[X] :=
  X ^ r - ∑ i : Fin r, C (c i) * X ^ (i : ℕ)

theorem krylovPolynomial_monic {K : Type*} [Field K] {r : ℕ} (c : Fin r → K) :
    (krylovPolynomial c).Monic :=
  monic_X_pow_sub (degree_sum_fin_lt c)

theorem krylovPolynomial_degree {K : Type*} [Field K] {r : ℕ} (c : Fin r → K) :
    (krylovPolynomial c).degree = r := by
  exact (degree_sub_eq_left_of_degree_lt (by simpa using degree_sum_fin_lt c)).trans
    (degree_X_pow r)

theorem aeval_krylovPolynomial_mulVec {K : Type*} [Field K] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (c : Fin r → K) :
    (aeval A (krylovPolynomial c)) *ᵥ u =
      krylovVector A u r - ∑ i : Fin r, c i • krylovVector A u i := by
  simp [krylovPolynomial, krylovVector, map_sum, Matrix.sub_mulVec, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

theorem krylovPolynomial_annihilates {K : Type*} [Field K] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (c : Fin r → K)
    (hdep : krylovVector A u r = ∑ i : Fin r, c i • krylovVector A u i) :
    (aeval A (krylovPolynomial c)) *ᵥ u = 0 := by
  rw [aeval_krylovPolynomial_mulVec, hdep, sub_self]

/-- Independence of the first `r` Krylov vectors rules out annihilators of degree below `r`. -/
theorem eq_zero_of_krylov_independent {K : Type*} [Field K] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (hind : LinearIndependent K (fun i : Fin r => krylovVector A u i))
    (h : K[X]) (hdegree : h.degree < r) (hann : (aeval A h) *ᵥ u = 0) : h = 0 := by
  classical
  have hexpand : h = ∑ i : Fin r, C (h.coeff i) * X ^ (i : ℕ) := by
    simpa only [C_mul_X_pow_eq_monomial, sum_monomial_eq] using
      (Polynomial.sum_fin (fun i a => monomial i a) (by simp) hdegree).symm
  have hsum : ∑ i : Fin r, h.coeff i • krylovVector A u i = 0 := by
    rw [hexpand] at hann
    simpa [krylovVector, map_sum, Matrix.sum_mulVec,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec] using hann
  have hc := Fintype.linearIndependent_iff.mp hind _ hsum
  rw [hexpand]
  simp [hc]

/-- At the first Krylov dependence, the explicit polynomial is the monic ideal generator. -/
theorem krylovPolynomial_eq_minimalAnnihilatingPolynomial (K : Subfield ℂ) {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (c : Fin r → K)
    (hind : LinearIndependent K (fun i : Fin r => krylovVector A u i))
    (hdep : krylovVector A u r = ∑ i : Fin r, c i • krylovVector A u i) :
    krylovPolynomial c = minimalAnnihilatingPolynomial K A u := by
  have hdiv := (minimalAnnihilatingPolynomial_dvd_iff K A u _).mpr
    (krylovPolynomial_annihilates A u c hdep)
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minimalAnnihilatingPolynomial_monic K A u) (krylovPolynomial_monic c) hdiv
  have hr : (krylovPolynomial c).natDegree = r :=
    natDegree_eq_of_degree_eq_some (krylovPolynomial_degree c)
  rw [hr]
  by_contra hn
  have hz := eq_zero_of_krylov_independent A u hind
    (minimalAnnihilatingPolynomial K A u)
    ((natDegree_lt_iff_degree_lt
      (minimalAnnihilatingPolynomial_monic K A u).ne_zero).mp (Nat.lt_of_not_ge hn))
    (minimalAnnihilatingPolynomial_annihilates K A u)
  exact (minimalAnnihilatingPolynomial_monic K A u).ne_zero hz

/-- The Krylov vectors before the degree of the minimal polynomial are independent. -/
theorem krylovVector_linearIndependent (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    LinearIndependent K (fun i : Fin (minimalAnnihilatingPolynomial K A u).natDegree =>
      krylovVector A u i) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  let q : K[X] := ∑ j : Fin (minimalAnnihilatingPolynomial K A u).natDegree,
    C (c j) * X ^ (j : ℕ)
  have hqann : (aeval A q) *ᵥ u = 0 := by
    simpa [q, krylovVector, map_sum, Matrix.sum_mulVec,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec] using hc
  have hqzero : q = 0 := by
    by_contra hq
    have hle := minimalAnnihilatingPolynomial_degree_le K A u q hq hqann
    have hlt := degree_sum_fin_lt c
    rw [← degree_eq_natDegree (minimalAnnihilatingPolynomial_monic K A u).ne_zero] at hlt
    exact (not_lt_of_ge hle) hlt
  have hcoeff := congrArg (fun p : K[X] => p.coeff i) hqzero
  simpa [q, C_mul_X_pow_eq_monomial, coeff_monomial, Fin.val_eq_val,
    Finset.sum_ite_eq'] using hcoeff

/-- Every monic polynomial can be reconstructed from the negatives of its lower coefficients. -/
theorem krylovPolynomial_neg_coeff {K : Type*} [Field K] (q : K[X]) (hq : q.Monic) :
    krylovPolynomial (fun i : Fin q.natDegree => -q.coeff i) = q := by
  classical
  have hexpand := q.as_sum_range_C_mul_X_pow
  rw [Finset.sum_range_succ, hq.coeff_natDegree, C_1, one_mul] at hexpand
  unfold krylovPolynomial
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i)]
  exact (add_comm _ _).trans hexpand.symm

/-- Coefficients of the explicit Krylov polynomial, in ascending order. -/
def krylovCoefficient {K : Type*} [Field K] {r : ℕ} (c : Fin r → K) (j : ℕ) : K :=
  if h : j < r then -c ⟨j, h⟩ else if j = r then 1 else 0

/-- An executable constructor, using decidable equality to compute the finite support.
The coefficients are supplied explicitly rather than extracted from an existence theorem. -/
def krylovPolynomialCompute {K : Type*} [Field K] [DecidableEq K] {r : ℕ}
    (c : Fin r → K) : K[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff {
    support := (Finset.range (r + 1)).filter (fun j => krylovCoefficient c j ≠ 0)
    toFun := krylovCoefficient c
    mem_support_toFun := by
      intro j
      simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      intro hj
      by_contra hbound
      have hgt : r < j := by omega
      simp [krylovCoefficient, Nat.not_lt_of_ge hgt.le, ne_of_gt hgt] at hj })

theorem krylovPolynomialCompute_eq {K : Type*} [Field K] [DecidableEq K] {r : ℕ}
    (c : Fin r → K) : krylovPolynomialCompute c = krylovPolynomial c := by
  ext j
  change krylovCoefficient c j = (krylovPolynomial c).coeff j
  simp only [krylovPolynomial, coeff_sub, coeff_X_pow, finsetSum_coeff,
    C_mul_X_pow_eq_monomial, coeff_monomial]
  by_cases hj : j < r
  · have hne : j ≠ r := ne_of_lt hj
    have hsum : (∑ i : Fin r, if (i : ℕ) = j then c i else 0) = c ⟨j, hj⟩ := by
      have heq (i : Fin r) : (i : ℕ) = j ↔ i = ⟨j, hj⟩ :=
        ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp [krylovCoefficient, hj, hne, hsum]
  · have hsum : (∑ i : Fin r, if (i : ℕ) = j then c i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : (i : ℕ) ≠ j := by intro h; exact hj (h ▸ i.isLt)
      simp [hne]
    rw [hsum]
    simp [krylovCoefficient, hj, eq_comm]

/-- The executable constructor returns the minimal polynomial when given a first dependence. -/
theorem krylovPolynomialCompute_eq_minimalAnnihilatingPolynomial (K : Subfield ℂ)
    [DecidableEq K] {n r : ℕ} (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (c : Fin r → K)
    (hind : LinearIndependent K (fun i : Fin r => krylovVector A u i))
    (hdep : krylovVector A u r = ∑ i : Fin r, c i • krylovVector A u i) :
    krylovPolynomialCompute c = minimalAnnihilatingPolynomial K A u := by
  rw [krylovPolynomialCompute_eq]
  exact krylovPolynomial_eq_minimalAnnihilatingPolynomial K A u c hind hdep

/-- A first Krylov dependence always occurs by step `n`, including step zero when `u = 0`.
This is an existence theorem, not an implementation of a linear-system solver. -/
theorem exists_first_krylov_relation (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    ∃ (r : ℕ) (c : Fin r → K), r ≤ n ∧
      LinearIndependent K (fun i : Fin r => krylovVector A u i) ∧
      krylovVector A u r = ∑ i : Fin r, c i • krylovVector A u i := by
  let q := minimalAnnihilatingPolynomial K A u
  refine ⟨q.natDegree, fun i => -q.coeff i, ?_, krylovVector_linearIndependent K A u, ?_⟩
  · have hdiv : q ∣ A.charpoly :=
      (minimalAnnihilatingPolynomial_dvd_iff K A u _).mpr
        (by simp [Matrix.aeval_self_charpoly])
    simpa using natDegree_le_of_dvd hdiv A.charpoly_monic.ne_zero
  · apply sub_eq_zero.mp
    rw [← aeval_krylovPolynomial_mulVec,
      krylovPolynomial_neg_coeff q (minimalAnnihilatingPolynomial_monic K A u)]
    exact minimalAnnihilatingPolynomial_annihilates K A u

end SympyProofs.JordanKrylov
