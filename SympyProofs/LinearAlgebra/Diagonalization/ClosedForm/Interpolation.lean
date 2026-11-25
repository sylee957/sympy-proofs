module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import SympyProofs.LinearAlgebra.Diagonalization.Basic
public import Mathlib.Tactic

/-!
# Constructing a finite eigenbasis from a list of roots

For each distinct root μ, evaluate its Lagrange basis polynomial at the matrix A.
The resulting matrices sum to the identity. Multilinearity of the determinant
then gives an invertible matrix whose j-th column is the j-th column of one
of these matrices. If the product of the distinct linear factors annihilates A,
each selected column is an eigenvector for its selected root.
-/

@[expose] public section

namespace SympyProofs.Diagonalization

open Lagrange Matrix Polynomial
open scoped Matrix

variable {n : ℕ}

variable {K : Type*} [Field K] [DecidableEq K]

/-- Evaluate the product of the distinct factors X - μ at A. -/
noncomputable def distinctFactorProduct (A : Matrix (Fin n) (Fin n) K) (roots : List K) :
    Matrix (Fin n) (Fin n) K :=
  aeval A (nodal roots.toFinset id)

/-- Column j comes from the Lagrange matrix for the root d j. -/
noncomputable def basisCandidate (A : Matrix (Fin n) (Fin n) K) (roots : List K) (d : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  of fun i j => (aeval A (Lagrange.basis roots.toFinset id (d j))) i j

/-- All assignments of a root to each column, in lexicographic list order. -/
def assignments {K : Type*} (roots : List K) : (n : ℕ) → List (Fin n → K)
  | 0 => [Fin.elim0]
  | n + 1 => roots.flatMap fun x => (assignments roots n).map (Fin.cons x)

omit [Field K] [DecidableEq K] in
private theorem mem_assignments {roots : List K} {d : Fin n → K} :
    d ∈ assignments roots n ↔ ∀ j, d j ∈ roots := by
  induction n with
  | zero => simp [assignments, Subsingleton.elim d Fin.elim0]
  | succ n ih =>
    simp only [assignments, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩ j
      exact Fin.cases hx (ih.mp ht) j
    · intro h
      exact ⟨d 0, h 0, Fin.tail d, ih.mpr (fun i => h i.succ), Fin.cons_self_tail d⟩

/-- Test the annihilator and take the first candidate with nonzero determinant.
With n input roots there are at most n^n determinant tests. -/
noncomputable def diagonalizeWith (A : Matrix (Fin n) (Fin n) K) (roots : List K) :
    Option (Matrix (Fin n) (Fin n) K × (Fin n → K)) :=
  if distinctFactorProduct A roots = 0 then
    ((assignments roots n).find? fun d => (basisCandidate A roots d).det ≠ 0).map
      fun d => (basisCandidate A roots d, d)
  else none

private theorem exists_invertible_candidate (A : Matrix (Fin n) (Fin n) K) (roots : List K)
    (hs : roots.toFinset.Nonempty) :
    ∃ d ∈ assignments roots n, (basisCandidate A roots d).det ≠ 0 := by
  let E (x : K) := aeval A (Lagrange.basis roots.toFinset id x)
  have hsum : ∑ x ∈ roots.toFinset, E x = 1 := by
    rw [show (∑ x ∈ roots.toFinset, E x) = aeval A (∑ x ∈ roots.toFinset,
        Lagrange.basis roots.toFinset id x) by simp [E]]
    rw [Lagrange.sum_basis Function.injective_id.injOn hs, map_one]
  let detRows := (detRowAlternating (n := Fin n) (R := K)).toMultilinearMap
  have hcols (j : Fin n) : ∑ x ∈ roots.toFinset, (E x).col j = (1 : Matrix (Fin n) (Fin n) K).col j := by
    funext i
    simpa [Matrix.col, Matrix.sum_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hsum
  have hexpand := detRows.map_sum_finset (fun j x => (E x).col j) (fun _ => roots.toFinset)
  simp only [hcols] at hexpand
  change (1 : Matrix (Fin n) (Fin n) K)ᵀ.det = ∑ d ∈ Fintype.piFinset (fun _ : Fin n => roots.toFinset),
    (basisCandidate A roots d)ᵀ.det at hexpand
  simp only [det_transpose, det_one] at hexpand
  obtain ⟨d, hd, hdet⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hexpand ▸ one_ne_zero)
  exact ⟨d, mem_assignments.mpr (fun j => List.mem_toFinset.mp (Fintype.mem_piFinset.mp hd j)), hdet⟩

private theorem eigen_columns {A : Matrix (Fin n) (Fin n) K} {roots : List K}
    (hz : distinctFactorProduct A roots = 0) {d : Fin n → K} (hd : d ∈ assignments roots n) :
    A * basisCandidate A roots d = basisCandidate A roots d * diagonal d := by
  ext i j
  have hj : d j ∈ roots.toFinset := List.mem_toFinset.mpr (mem_assignments.mp hd j)
  let L := Lagrange.basis roots.toFinset id (d j)
  have hpoly : (X - C (d j)) * L =
      C (nodalWeight roots.toFinset id (d j)) * nodal roots.toFinset id := by
    rw [show L = _ from basis_eq_prod_sub_inv_mul_nodal_div hj,
      ← nodal_erase_eq_nodal_div hj, nodal_eq_mul_nodal_erase hj]
    simp only [id_eq]
    ac_rfl
  have hzero := congrArg (aeval A) hpoly
  unfold distinctFactorProduct at hz
  simp only [map_mul, map_sub, aeval_X, aeval_C, hz, mul_zero,
    sub_mul, sub_eq_zero] at hzero
  rw [mul_diagonal]
  change (A * aeval A L) i j = (aeval A L) i j * d j
  rw [hzero, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  simp [mul_comm]

/-- Every successful return is a diagonalization, even for an arbitrary input list. -/
theorem diagonalizeWith_sound {A P : Matrix (Fin n) (Fin n) K} {roots : List K} {d : Fin n → K}
    (h : diagonalizeWith A roots = some (P, d)) : IsDiagonalization A P d := by
  unfold diagonalizeWith at h
  split at h <;> simp only [Option.map_eq_some_iff, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨e, he, rfl, rfl⟩ := h
  have hdet := List.find?_some he
  simp only [decide_eq_true_eq] at hdet
  refine ⟨hdet, ?_⟩
  rw [← eigen_columns ‹_› (List.mem_of_find?_eq_some he)]
  exact (Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hdet)).symm

/-- The determinant search always succeeds when the distinct-factor product vanishes. -/
theorem diagonalizeWith_isSome [NeZero n] {A : Matrix (Fin n) (Fin n) K} {roots : List K} :
    (diagonalizeWith A roots).isSome ↔ distinctFactorProduct A roots = 0 := by
  by_cases hz : distinctFactorProduct A roots = 0
  · have hs : roots.toFinset.Nonempty := by
      by_contra! he
      simp [distinctFactorProduct, he, nodal] at hz
    obtain ⟨d, hd, hdet⟩ := exists_invertible_candidate A roots hs
    simp only [diagonalizeWith, hz, ite_true, Option.isSome_map, List.isSome_find?, List.any_eq_true,
      decide_eq_true_eq, iff_true]
    exact ⟨d, hd, hdet⟩
  · simp [diagonalizeWith, hz]

omit [DecidableEq K] in
theorem aeval_mul_basis {A P : Matrix (Fin n) (Fin n) K} {d : Fin n → K}
    (h : A * P = P * diagonal d) (p : K[X]) :
    aeval A p * P = P * diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul, hp, hq, eval_add, ← mul_add, ← diagonal_add]
  | monomial n c =>
    have hpow := (show SemiconjBy P (diagonal d) A from h.symm).pow_right n
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, ← hpow.eq, diagonal_pow]
    rw [← mul_smul_comm, ← diagonal_smul]
    rfl

/-- Any existing diagonalization forces the test to succeed when the input list
contains every root of the characteristic polynomial over the base field. -/
theorem diagonalizeWith_complete [NeZero n] {A P : Matrix (Fin n) (Fin n) K}
    {d : Fin n → K} {roots : List K}
    (h : IsDiagonalization A P d) (cover : ∀ x, A.charpoly.eval x = 0 → x ∈ roots) :
    (diagonalizeWith A roots).isSome := by
  obtain ⟨hdet, hA⟩ := h
  have hu := isUnit_iff_ne_zero.mpr hdet
  have hinter : A * P = P * diagonal d := by
    rw [hA, mul_assoc, P.nonsing_inv_mul hu, mul_one]
  have hchar : A.charpoly = (diagonal d).charpoly := by
    let U := P.nonsingInvUnit hu
    rw [hA]
    exact Matrix.charpoly_units_conj U _
  have hmem (i : Fin n) : d i ∈ roots.toFinset := by
    apply List.mem_toFinset.mpr
    apply cover
    rw [hchar, charpoly_diagonal, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have heval (i : Fin n) : (nodal roots.toFinset id).eval (d i) = 0 :=
    eval_nodal_at_node (v := id) (hmem i)
  have hzero := aeval_mul_basis hinter (nodal roots.toFinset id)
  simp only [heval, diagonal_zero, mul_zero] at hzero
  apply diagonalizeWith_isSome.mpr
  change aeval A _ = 0
  rw [← P.mul_nonsing_inv_cancel_right (aeval A _) hu, hzero, zero_mul]

/-- Covering all characteristic roots makes the search succeed exactly on diagonalizable inputs. -/
theorem diagonalizeWith_isSome_iff [NeZero n] (A : Matrix (Fin n) (Fin n) K) {xs : List K}
    (cover : ∀ x, A.charpoly.eval x = 0 → x ∈ xs) :
    (diagonalizeWith A xs).isSome ↔ ∃ P d, IsDiagonalization A P d := by
  constructor
  · intro h
    obtain ⟨⟨P, d⟩, hd⟩ := Option.isSome_iff_exists.mp h
    exact ⟨P, d, diagonalizeWith_sound hd⟩
  · rintro ⟨P, d, hd⟩
    exact diagonalizeWith_complete hd cover

end SympyProofs.Diagonalization
