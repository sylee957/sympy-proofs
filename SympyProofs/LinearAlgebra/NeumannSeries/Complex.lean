module

public import SympyProofs.LinearAlgebra.NeumannSeries.Algebraic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Complex matrix series reduced to real matrix series by realification. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

variable {n : Type*}

/-- The real matrix acting on the real and imaginary parts of a complex vector. -/
def realify (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (A.map Complex.re) (-(A.map Complex.im))
    (A.map Complex.im) (A.map Complex.re)

@[simp] theorem realify_sub (A B : Matrix n n ℂ) :
    realify (A - B) = realify A - realify B := by
  ext i j
  cases i <;> cases j <;> simp [realify]
  abel

@[simp] theorem realify_conjTranspose (A : Matrix n n ℂ) :
    realify Aᴴ = (realify A)ᵀ := by
  ext i j
  cases i <;> cases j <;> simp [realify, conjTranspose_apply]

lemma summable_complex_iff_re_im {ι : Type*} (f : ι → ℂ) :
    Summable f ↔ Summable (fun i => (f i).re) ∧ Summable (fun i => (f i).im) := by
  constructor
  · intro h
    exact ⟨Complex.reCLM.summable h, Complex.imCLM.summable h⟩
  · rintro ⟨hr, hi⟩
    simpa only [Complex.ofRealCLM_apply, Complex.re_add_im] using
      (Complex.ofRealCLM.summable hr).add ((Complex.ofRealCLM.summable hi).mul_right Complex.I)

lemma summable_matrix_iff_entries {ι R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (f : ι → Matrix n n R) : Summable f ↔ ∀ i j, Summable (fun k => f k i j) := by
  exact Pi.summable.trans (forall_congr' (fun _ => Pi.summable))

theorem summable_realify_iff {ι : Type*} (f : ι → Matrix n n ℂ) :
    Summable (fun k => realify (f k)) ↔ Summable f := by
  simp only [summable_matrix_iff_entries]
  constructor
  · intro h i j
    apply (summable_complex_iff_re_im _).mpr
    exact ⟨h (Sum.inl i) (Sum.inl j), h (Sum.inr i) (Sum.inl j)⟩
  · intro h i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact (summable_complex_iff_re_im _).mp (h i j) |>.1
      | inr j => exact ((summable_complex_iff_re_im _).mp (h i j) |>.2).neg
    | inr i =>
      cases j with
      | inl j => exact (summable_complex_iff_re_im _).mp (h i j) |>.2
      | inr j => exact (summable_complex_iff_re_im _).mp (h i j) |>.1

@[simp] theorem realify_one [DecidableEq n] : realify (1 : Matrix n n ℂ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.one_apply, apply_ite]

section FiniteMatrices

variable [Fintype n]

theorem realify_mul (A B : Matrix n n ℂ) : realify (A * B) = realify A * realify B := by
  unfold realify
  rw [fromBlocks_multiply]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  all_goals abel

theorem realify_stein (A P : Matrix n n ℂ) :
    realify (P - Aᴴ * P * A) = stein (realify A) (realify P) := by
  simp only [realify_sub, realify_mul, realify_conjTranspose, stein]

variable [DecidableEq n]

@[simp] theorem realify_pow (A : Matrix n n ℂ) (k : ℕ) : realify (A ^ k) = realify A ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, realify_mul, ih, pow_succ]

theorem summable_complex_pow_iff_realify (A : Matrix n n ℂ) :
    Summable (fun k : ℕ => A ^ k) ↔ Summable (fun k : ℕ => realify A ^ k) := by
  simpa only [realify_pow] using (summable_realify_iff (fun k : ℕ => A ^ k)).symm

end FiniteMatrices

/-- The same realification, reindexed consecutively for the leading-minor criterion. -/
def realifyFin {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (m + m)) (Fin (m + m)) ℝ :=
  (Matrix.reindexRingEquiv ℝ finSumFinEquiv) (realify A)

@[simp] theorem realifyFin_pow {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    realifyFin (A ^ k) = realifyFin A ^ k := by
  rw [realifyFin, realify_pow, map_pow]
  rfl

theorem summable_realifyFin_iff {ι : Type*} {m : ℕ} (f : ι → Matrix (Fin m) (Fin m) ℂ) :
    Summable (fun k => realifyFin (f k)) ↔ Summable f := by
  rw [← summable_realify_iff f]
  simp only [summable_matrix_iff_entries]
  constructor
  · intro h i j
    simpa [realifyFin, Matrix.reindex_apply] using h (finSumFinEquiv i) (finSumFinEquiv j)
  · intro h i j
    exact h (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

/-- A finite conjunction of real polynomial inequalities in the real and imaginary entries. -/
def complexAlgebraicCondition {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  algebraicCondition (realifyFin A)

theorem summable_complex_pow_iff_algebraicCondition {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    Summable (fun k : ℕ => A ^ k) ↔ complexAlgebraicCondition A := by
  rw [← summable_realifyFin_iff (fun k : ℕ => A ^ k)]
  simp only [realifyFin_pow, complexAlgebraicCondition, summable_pow_iff_algebraicCondition]

theorem hasSum_inverse_of_complexAlgebraicCondition {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} (h : complexAlgebraicCondition A) :
    HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ :=
  hasSum_inverse ((summable_complex_pow_iff_algebraicCondition A).mpr h)

end SympyProofs.NeumannSeries
