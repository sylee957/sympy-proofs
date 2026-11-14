module

public import SympyProofs.LinearAlgebra.NeumannSeries.Complex
public import SympyProofs.LinearAlgebra.NeumannSeries.Rational

/-! Real polynomial certificates for matrices with complex polynomial or rational entries. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

/-- Assemble the real and imaginary component matrices. -/
def ofRealImag {n : Type*} (X Y : Matrix n n ℝ) : Matrix n n ℂ :=
  of (fun i j => (X i j : ℂ) + (Y i j : ℂ) * Complex.I)

/-- The real block construction works over the polynomial coefficient ring itself. -/
def blockRealification {R : Type*} [Ring R] {m : ℕ}
    (X Y : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  (Matrix.reindexRingEquiv R finSumFinEquiv) (fromBlocks X (-Y) Y X)

lemma realifyFin_ofRealImag {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℝ) :
    realifyFin (ofRealImag X Y) = blockRealification X Y := by
  have hx : (ofRealImag X Y).map Complex.re = X := by ext i j; simp [ofRealImag]
  have hy : (ofRealImag X Y).map Complex.im = Y := by ext i j; simp [ofRealImag]
  simp only [realifyFin, realify, hx, hy, blockRealification]

lemma blockRealification_map {R S : Type*} [Ring R] [Ring S] {m : ℕ}
    (X Y : Matrix (Fin m) (Fin m) R) (f : R →+* S) :
    blockRealification (X.map f) (Y.map f) = (blockRealification X Y).map f := by
  have hn : (-Y).map f = -(Y.map f) := by ext i j; simp
  simp only [blockRealification, coe_reindexRingEquiv, reindex_apply,
    ← submatrix_map, fromBlocks_map, hn]

lemma blockRealification_smul {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    blockRealification (c • X) (c • Y) = c • blockRealification X Y := by
  simp only [blockRealification, coe_reindexRingEquiv, reindex_apply, ← smul_neg,
    ← fromBlocks_smul, submatrix_smul]
  rfl

theorem summable_ofRealImag_pow_iff {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℝ) :
    Summable (fun k : ℕ => ofRealImag X Y ^ k) ↔
      Summable (fun k : ℕ => blockRealification X Y ^ k) := by
  rw [← summable_realifyFin_iff (fun k : ℕ => ofRealImag X Y ^ k)]
  simp only [realifyFin_pow, realifyFin_ofRealImag]

/-- The complex entries are `X(θ) + i Y(θ)`; every condition is a real polynomial sign. -/
theorem complex_polynomial_convergence_iff {σ : Type*} {m : ℕ}
    (X Y : Matrix (Fin m) (Fin m) (MvPolynomial σ ℚ)) (θ : σ → ℝ) :
    let ev := MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) θ
    Summable (fun k : ℕ => ofRealImag (X.map ev) (Y.map ev) ^ k) ↔
      ev (denominator (blockRealification X Y)) ≠ 0 ∧
        ∀ k : Fin (m + m + 1), 0 < ev (signPolynomial (blockRealification X Y) k) := by
  dsimp only
  rw [summable_ofRealImag_pow_iff, blockRealification_map]
  exact polynomial_convergence_iff (blockRealification X Y) θ

/-- Real and imaginary rational entries share a real polynomial denominator `c`. -/
theorem complex_rational_polynomial_convergence_iff {σ : Type*} {m : ℕ}
    (X Y : Matrix (Fin m) (Fin m) (MvPolynomial σ ℚ))
    (c : MvPolynomial σ ℚ) (θ : σ → ℝ) :
    let ev := MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) θ
    (ev c ≠ 0 ∧ Summable (fun k : ℕ =>
      ofRealImag ((ev c)⁻¹ • X.map ev) ((ev c)⁻¹ • Y.map ev) ^ k)) ↔
      ev c ≠ 0 ∧ ev (clearedDenominator (blockRealification X Y) c) ≠ 0 ∧
        ∀ k : Fin (m + m + 1), 0 < ev (clearedSignPolynomial (blockRealification X Y) c k) := by
  dsimp only
  rw [summable_ofRealImag_pow_iff, blockRealification_smul, blockRealification_map]
  exact rational_polynomial_convergence_iff (blockRealification X Y) c θ

end SympyProofs.NeumannSeries
