import SympyProofs.MoorePenrose.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Faddeev–LeVerrier recurrence

The recurrence is defined over any commutative rational algebra, including
polynomial rings. Its only divisions are by the positive integers indexing
the steps. In particular, no matrix entry or pivot is inverted here.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix Polynomial

section Recurrence

variable {R n : Type*} [CommRing R] [Algebra ℚ R] [Fintype n] [DecidableEq n]

/-- The coefficient and residual matrix at step `k`. -/
def state (G : Matrix n n R) : ℕ → R × Matrix n n R
  | 0 => (1, 1)
  | k + 1 =>
    let H := G * (state G k).2
    let e := ((k + 1 : ℚ)⁻¹) • H.trace
    (e, e • 1 - H)

/-- The `k`th elementary characteristic coefficient (with positive sign). -/
def coeff (G : Matrix n n R) (k : ℕ) : R := (state G k).1

/-- The residual `Fₖ`, starting at the identity. -/
def residual (G : Matrix n n R) (k : ℕ) : Matrix n n R := (state G k).2

@[simp] theorem coeff_zero (G : Matrix n n R) : coeff G 0 = 1 := rfl
@[simp] theorem residual_zero (G : Matrix n n R) : residual G 0 = 1 := rfl

theorem coeff_succ (G : Matrix n n R) (k : ℕ) :
    coeff G (k + 1) = ((k + 1 : ℚ)⁻¹) • (G * residual G k).trace := rfl

theorem residual_succ (G : Matrix n n R) (k : ℕ) :
    residual G (k + 1) = coeff G (k + 1) • 1 - G * residual G k := rfl

/-- Every residual commutes with the input matrix. -/
theorem residual_commute (G : Matrix n n R) (k : ℕ) :
    G * residual G k = residual G k * G := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [residual_succ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    exact (congrArg (fun H => G * H) ih).trans (Matrix.mul_assoc _ _ _).symm

/-- Specialization commutes with the recurrence, including at vanishing pivots. -/
theorem state_map {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (G : Matrix n n R) (k : ℕ) :
    state (G.map f) k = (f (coeff G k), (residual G k).map f) := by
  induction k with
  | zero => simp [state, coeff, residual]
  | succ k ih =>
    simp only [state, ih]
    change _ = (f (coeff G (k + 1)), (residual G (k + 1)).map f)
    rw [coeff_succ, residual_succ, coeff_succ]
    have hmul : G.map f * (residual G k).map f = (G * residual G k).map f := by
      ext i j
      simp [Matrix.mul_apply, map_sum, map_mul]
    have htrace : ((G * residual G k).map f).trace = f (G * residual G k).trace := by
      change (∑ i, f ((G * residual G k) i i)) = f (∑ i, (G * residual G k) i i)
      rw [map_sum]
    rw [hmul, htrace, map_smul]
    refine Prod.ext rfl ?_
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      map_sub, map_mul, map_smul, Matrix.one_apply]
    split_ifs <;> simp

end Recurrence

section GeneratingPolynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Generating polynomial of elementary symmetric functions on a finite set. -/
noncomputable def spectralPolynomial (d : n → R) (s : Finset n) : R[X] :=
  ∏ i ∈ s, (1 + C (d i) * X)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem spectralPolynomial_coeff_zero (d : n → R) (s : Finset n) :
    (spectralPolynomial d s).coeff 0 = 1 := by
  simp [spectralPolynomial, coeff_zero_eq_eval_zero, eval_prod]

/-- Removing one factor gives the coefficient recurrence for residual eigenvalues. -/
theorem spectralPolynomial_erase (d : n → R) (i : n) (k : ℕ) :
    (spectralPolynomial d Finset.univ).coeff (k + 1) =
      (spectralPolynomial d (Finset.univ.erase i)).coeff (k + 1) +
        d i * (spectralPolynomial d (Finset.univ.erase i)).coeff k := by
  have h : spectralPolynomial d Finset.univ =
      (1 + C (d i) * X) * spectralPolynomial d (Finset.univ.erase i) := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [h, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

/-- Differentiating the product gives the trace identity used by Faddeev. -/
theorem spectralPolynomial_trace (d : n → R) (k : ℕ) :
    ∑ i, d i * (spectralPolynomial d (Finset.univ.erase i)).coeff k =
      (spectralPolynomial d Finset.univ).coeff (k + 1) * (k + 1 : ℕ) := by
  have h := congrArg (fun p : R[X] => p.coeff k)
    (Polynomial.derivative_prod_finset (s := Finset.univ)
      (f := fun i => (1 + C (d i) * X : R[X])))
  simp only [derivative_add, derivative_one, derivative_mul, derivative_C,
    zero_mul, zero_add, derivative_X, mul_one, finsetSum_coeff, coeff_mul_C,
    coeff_derivative] at h
  simpa only [spectralPolynomial, mul_comm, Nat.cast_add, Nat.cast_one] using h.symm

end GeneratingPolynomial

end SympyProofs.MoorePenrose.Faddeev
