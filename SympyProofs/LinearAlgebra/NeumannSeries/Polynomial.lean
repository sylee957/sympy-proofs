module

public import SympyProofs.LinearAlgebra.NeumannSeries.Algebraic
public import Mathlib.Algebra.MvPolynomial.Eval

/-! Construction and specialization of polynomial convergence conditions. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

section FiniteMatrices

variable {n : Type*} [DecidableEq n]

lemma steinMatrix_map (A : Matrix n n R) (f : R →+* S) :
    steinMatrix (A.map f) = (steinMatrix A).map f := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [steinMatrix, Matrix.map_apply, Matrix.one_apply]

variable [Fintype n]

lemma denominator_map (A : Matrix n n R) (f : R →+* S) :
    denominator (A.map f) = f (denominator A) := by
  rw [denominator, steinMatrix_map]
  exact (f.map_det _).symm

lemma numerator_map (A : Matrix n n R) (f : R →+* S) :
    numerator (A.map f) = (numerator A).map f := by
  have hb : f ∘ vec (1 : Matrix n n R) = vec (1 : Matrix n n S) := by
    ext ⟨i, j⟩
    simp [vec, Matrix.one_apply]
  have ha : ((steinMatrix A).map f).adjugate = ((steinMatrix A).adjugate).map f :=
    (f.map_adjugate _).symm
  ext i j
  simp only [numerator, steinMatrix_map, ha, unvec, Matrix.map_apply]
  rw [f.map_mulVec, hb]

end FiniteMatrices

lemma leading_map {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (k : Fin (m + 1)) (f : R →+* S) :
    leading (P.map f) k = (leading P k).map f := rfl

/-- Each sign test is itself a polynomial when the entries of `A` are polynomials. -/
def signPolynomial {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (k : Fin (m + 1)) : R :=
  denominator A ^ k.val * (leading (numerator A) k).det

theorem summable_pow_map_iff {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (f : R →+* ℝ) :
    Summable (fun k : ℕ => (A.map f) ^ k) ↔
      f (denominator A) ≠ 0 ∧ ∀ k : Fin (m + 1), 0 < f (signPolynomial A k) := by
  rw [summable_pow_iff_algebraicCondition]
  simp only [algebraicCondition, denominator_map, numerator_map, leading_map,
    signPolynomial, map_mul, map_pow, RingHom.map_det, RingHom.mapMatrix_apply]

/-- Exact specialization theorem for a matrix with rational polynomial entries. -/
theorem polynomial_convergence_iff {σ : Type*} {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (MvPolynomial σ ℚ)) (θ : σ → ℝ) :
    let ev := MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) θ
    Summable (fun k : ℕ => (A.map ev) ^ k) ↔
      ev (denominator A) ≠ 0 ∧ ∀ k : Fin (m + 1), 0 < ev (signPolynomial A k) := by
  exact summable_pow_map_iff A _

end SympyProofs.NeumannSeries
