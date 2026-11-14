module

public import SympyProofs.LinearAlgebra.NeumannSeries.Polynomial

/-! Polynomial conditions for `A = c⁻¹ • N`, retaining the domain condition `c ≠ 0`. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Matrix
open scoped Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

section FiniteMatrices

variable {n : Type*} [DecidableEq n]

def clearedSteinMatrix (N : Matrix n n R) (c : R) : Matrix (n × n) (n × n) R :=
  c ^ 2 • 1 - of (fun ij kl => N kl.1 ij.1 * N kl.2 ij.2)

lemma clearedSteinMatrix_eq (N : Matrix n n ℝ) {c : ℝ} (hc : c ≠ 0) :
    clearedSteinMatrix N c = c ^ 2 • steinMatrix (c⁻¹ • N) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [clearedSteinMatrix, steinMatrix, Matrix.smul_apply, smul_eq_mul]
  field_simp

lemma clearedSteinMatrix_map (N : Matrix n n R) (c : R) (f : R →+* S) :
    clearedSteinMatrix (N.map f) (f c) = (clearedSteinMatrix N c).map f := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [clearedSteinMatrix, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

variable [Fintype n]

def clearedDenominator (N : Matrix n n R) (c : R) : R := (clearedSteinMatrix N c).det

def clearedNumerator (N : Matrix n n R) (c : R) : Matrix n n R :=
  unvec ((clearedSteinMatrix N c).adjugate *ᵥ vec (c ^ 2 • (1 : Matrix n n R)))

lemma clearedDenominator_ne_zero_iff (N : Matrix n n ℝ) {c : ℝ} (hc : c ≠ 0) :
    clearedDenominator N c ≠ 0 ↔ denominator (c⁻¹ • N) ≠ 0 := by
  rw [clearedDenominator, clearedSteinMatrix_eq N hc, det_smul]
  simp [denominator, hc]

lemma clearedNumerator_eq (N : Matrix n n ℝ) {c : ℝ} (hc : c ≠ 0)
    (hd : denominator (c⁻¹ • N) ≠ 0) :
    clearedNumerator N c = clearedDenominator N c • candidate (c⁻¹ • N) := by
  have he : clearedSteinMatrix N c *ᵥ vec (candidate (c⁻¹ • N)) =
      vec (c ^ 2 • (1 : Matrix n n ℝ)) := by
    rw [clearedSteinMatrix_eq N hc, smul_mulVec, steinMatrix_mulVec, stein_candidate hd]
    rfl
  apply vec_injective
  change (clearedSteinMatrix N c).adjugate *ᵥ vec (c ^ 2 • (1 : Matrix n n ℝ)) = _
  rw [← he, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rfl

lemma clearedDenominator_map (N : Matrix n n R) (c : R) (f : R →+* S) :
    clearedDenominator (N.map f) (f c) = f (clearedDenominator N c) := by
  rw [clearedDenominator, clearedSteinMatrix_map]
  exact (f.map_det _).symm

lemma clearedNumerator_map (N : Matrix n n R) (c : R) (f : R →+* S) :
    clearedNumerator (N.map f) (f c) = (clearedNumerator N c).map f := by
  have hb : f ∘ vec (c ^ 2 • (1 : Matrix n n R)) =
      vec ((f c) ^ 2 • (1 : Matrix n n S)) := by
    ext ⟨i, j⟩
    simp [vec, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have ha : ((clearedSteinMatrix N c).map f).adjugate =
      ((clearedSteinMatrix N c).adjugate).map f := (f.map_adjugate _).symm
  ext i j
  simp only [clearedNumerator, clearedSteinMatrix_map, ha, unvec, Matrix.map_apply]
  rw [f.map_mulVec, hb]

end FiniteMatrices

def clearedSignPolynomial {m : ℕ} (N : Matrix (Fin m) (Fin m) R)
    (c : R) (k : Fin (m + 1)) : R :=
  clearedDenominator N c ^ k.val * (leading (clearedNumerator N c) k).det

lemma clearedSign_pos_iff {m : ℕ} (N : Matrix (Fin m) (Fin m) ℝ)
    {c : ℝ} (hc : c ≠ 0) (hd : denominator (c⁻¹ • N) ≠ 0) (k : Fin (m + 1)) :
    0 < clearedSignPolynomial N c k ↔ 0 < (leading (candidate (c⁻¹ • N)) k).det := by
  have hd' := (clearedDenominator_ne_zero_iff N hc).mpr hd
  rw [clearedSignPolynomial, clearedNumerator_eq N hc hd]
  change 0 < clearedDenominator N c ^ k.val *
    (clearedDenominator N c • leading (candidate (c⁻¹ • N)) k).det ↔ _
  rw [det_smul, Fintype.card_fin, ← mul_assoc, ← pow_two]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (pow_ne_zero _ hd'))

/-- The domain guard and convergence are jointly expressed by polynomial signs. -/
theorem rational_convergence_iff {m : ℕ} (N : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    (c ≠ 0 ∧ Summable (fun k : ℕ => (c⁻¹ • N) ^ k)) ↔
      c ≠ 0 ∧ clearedDenominator N c ≠ 0 ∧
        ∀ k : Fin (m + 1), 0 < clearedSignPolynomial N c k := by
  apply and_congr_right
  intro hc
  rw [summable_pow_iff_candidate, clearedDenominator_ne_zero_iff N hc]
  apply and_congr_right
  intro hd
  rw [posDef_iff_leading_pos, and_iff_right (candidate_isHermitian hd)]
  exact forall_congr' (fun k => (clearedSign_pos_iff N hc hd k).symm)

lemma clearedSignPolynomial_map {m : ℕ} (N : Matrix (Fin m) (Fin m) R)
    (c : R) (k : Fin (m + 1)) (f : R →+* S) :
    clearedSignPolynomial (N.map f) (f c) k = f (clearedSignPolynomial N c k) := by
  simp only [clearedSignPolynomial, clearedDenominator_map, clearedNumerator_map,
    leading_map, map_mul, map_pow, RingHom.map_det, RingHom.mapMatrix_apply]

/-- Polynomial specialization with a common denominator, including its excluded zero set. -/
theorem rational_polynomial_convergence_iff {σ : Type*} {m : ℕ}
    (N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℚ)) (c : MvPolynomial σ ℚ) (θ : σ → ℝ) :
    let ev := MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) θ
    (ev c ≠ 0 ∧ Summable (fun k : ℕ => ((ev c)⁻¹ • N.map ev) ^ k)) ↔
      ev c ≠ 0 ∧ ev (clearedDenominator N c) ≠ 0 ∧
        ∀ k : Fin (m + 1), 0 < ev (clearedSignPolynomial N c k) := by
  dsimp only
  rw [rational_convergence_iff, clearedDenominator_map]
  simp only [clearedSignPolynomial_map]

end SympyProofs.NeumannSeries
