import SympyProofs.MoorePenrose.Faddeev.Basic
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral correctness of Faddeev–LeVerrier

The generating polynomial is used only in the proof. The algorithm itself
uses matrix multiplication, trace, and rational constants.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix Polynomial

section Diagonal

variable {K n : Type*} [Field K] [CharZero K] [Algebra ℚ K]
  [Fintype n] [DecidableEq n]

theorem state_diagonal (d : n → K) (k : ℕ) :
    state (diagonal d) k =
      ((spectralPolynomial d Finset.univ).coeff k,
        diagonal fun i => (spectralPolynomial d (Finset.univ.erase i)).coeff k) := by
  induction k with
  | zero => simp [state]
  | succ k ih =>
    simp only [state, ih]
    have ht : (diagonal d *
        diagonal (fun i => (spectralPolynomial d (Finset.univ.erase i)).coeff k)).trace =
        (spectralPolynomial d Finset.univ).coeff (k + 1) * (k + 1 : ℕ) := by
      rw [diagonal_mul_diagonal, trace_diagonal]
      exact spectralPolynomial_trace d k
    rw [ht]
    have hc (x : K) : ((k + 1 : ℚ)⁻¹) • (x * (k + 1 : ℕ)) = x := by
      have hk : (k + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp [Algebra.smul_def, mul_comm, hk]
    rw [hc]
    refine Prod.ext rfl ?_
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
        mul_one, diagonal_mul_diagonal, diagonal_apply_eq]
      rw [spectralPolynomial_erase d i k]
      ring
    · simp [Matrix.sub_apply, Matrix.smul_apply, diagonal_mul_diagonal, hij]

variable [DecidableEq K]

omit [Algebra ℚ K] [DecidableEq n] in
/-- The generating polynomial has degree equal to the number of nonzero entries. -/
theorem spectralPolynomial_natDegree (d : n → K) :
    (spectralPolynomial d Finset.univ).natDegree = Fintype.card {i // d i ≠ 0} := by
  classical
  have hn (i : n) : (1 + C (d i) * X : K[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : K[X] => p.coeff 0) h
    simp at this
  unfold spectralPolynomial
  rw [natDegree_prod _ _ (fun i _ => hn i)]
  have hd (i : n) : (1 + C (d i) * X : K[X]).natDegree = if d i = 0 then 0 else 1 := by
    by_cases hi : d i = 0
    · simp [hi]
    · simp [natDegree_C_mul_X _ hi, hi]
  simp_rw [hd]
  simp [Fintype.card_subtype, Finset.card_filter]

omit [Algebra ℚ K] [DecidableEq K] [Fintype n] [DecidableEq n] in
theorem spectralPolynomial_ne_zero (d : n → K) (s : Finset n) :
    spectralPolynomial d s ≠ 0 := by
  intro h
  have := spectralPolynomial_coeff_zero d s
  rw [h, Polynomial.coeff_zero] at this
  exact zero_ne_one this

omit [Algebra ℚ K] [DecidableEq n] in
/-- The top coefficient never vanishes, even when individual entries do. -/
theorem spectralPolynomial_top_ne_zero (d : n → K) :
    (spectralPolynomial d Finset.univ).coeff (Fintype.card {i // d i ≠ 0}) ≠ 0 := by
  rw [← spectralPolynomial_natDegree]
  exact leadingCoeff_ne_zero.mpr (spectralPolynomial_ne_zero d _)

omit [Algebra ℚ K] in
/-- The terminal residual vanishes on every nonzero eigenspace. -/
theorem spectralPolynomial_erase_top (d : n → K) (i : n) :
    d i * (spectralPolynomial d (Finset.univ.erase i)).coeff
      (Fintype.card {i // d i ≠ 0}) = 0 := by
  by_cases hi : d i = 0
  · simp [hi]
  have h : spectralPolynomial d Finset.univ =
      (1 + C (d i) * X) * spectralPolynomial d (Finset.univ.erase i) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hn : (1 + C (d i) * X : K[X]) ≠ 0 := by
    intro hz
    have := congrArg (fun p : K[X] => p.coeff 0) hz
    simp at this
  have hd := congrArg Polynomial.natDegree h
  rw [spectralPolynomial_natDegree, natDegree_mul hn (spectralPolynomial_ne_zero d _),
    natDegree_one_add, natDegree_C_mul_X _ hi] at hd
  rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

end Diagonal

section Hermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem trace_unitary_conj (U : Matrix.unitaryGroup n 𝕜) (H : Matrix n n 𝕜) :
    (Unitary.conjStarAlgAut 𝕜 _ U H).trace = H.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

/-- Changing orthonormal basis conjugates every residual and preserves coefficients. -/
theorem state_unitary_conj (U : Matrix.unitaryGroup n 𝕜) (G : Matrix n n 𝕜) (k : ℕ) :
    state (Unitary.conjStarAlgAut 𝕜 _ U G) k =
      (coeff G k, Unitary.conjStarAlgAut 𝕜 _ U (residual G k)) := by
  induction k with
  | zero => simp [state, coeff, residual]
  | succ k ih =>
    simp only [state, ih]
    rw [← map_mul, trace_unitary_conj]
    rw [residual_succ]
    simp only [map_sub, map_smul, map_one, map_mul, coeff_succ]

/-- Hermitian input gives self-conjugate coefficients and Hermitian residuals. -/
theorem state_hermitian {G : Matrix n n 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    star (coeff G k) = coeff G k ∧ (residual G k).IsHermitian := by
  induction k with
  | zero => simp [Matrix.IsHermitian]
  | succ k ih =>
    have hH : (G * residual G k).IsHermitian := by
      change (G * residual G k)ᴴ = G * residual G k
      rw [Matrix.conjTranspose_mul, ih.2.eq, hG.eq, residual_commute]
    have ht : star (G * residual G k).trace = (G * residual G k).trace := by
      rw [← Matrix.trace_conjTranspose, hH.eq]
    have hc : star (coeff G (k + 1)) = coeff G (k + 1) := by
      simp [coeff_succ, ht]
    refine ⟨hc, ?_⟩
    change (residual G (k + 1))ᴴ = residual G (k + 1)
    rw [residual_succ, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hc, hH.eq]

/-- The spectral characterization of the recurrence, for every step. -/
theorem state_spectral {G : Matrix n n 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    state G k =
      ((spectralPolynomial (fun i => (hG.eigenvalues i : 𝕜)) Finset.univ).coeff k,
        Unitary.conjStarAlgAut 𝕜 _ hG.eigenvectorUnitary
          (diagonal fun i => (spectralPolynomial (fun j => (hG.eigenvalues j : 𝕜))
            (Finset.univ.erase i)).coeff k)) := by
  conv_lhs => rw [hG.spectral_theorem]
  rw [state_unitary_conj]
  simp only [coeff, residual, state_diagonal, Function.comp_def]

/-- The denominator at the actual rank is nonzero. No pivot hypothesis occurs. -/
theorem coeff_rank_ne_zero {G : Matrix n n 𝕜} (hG : G.IsHermitian) :
    coeff G G.rank ≠ 0 := by
  classical
  have hc := congrArg Prod.fst (state_spectral hG G.rank)
  change coeff G G.rank = _ at hc
  rw [hc, hG.rank_eq_card_non_zero_eigs]
  simpa only [RCLike.ofReal_ne_zero] using
    spectralPolynomial_top_ne_zero (fun i => (hG.eigenvalues i : 𝕜))

/-- At the actual rank, the residual annihilates the matrix. -/
theorem mul_residual_rank {G : Matrix n n 𝕜} (hG : G.IsHermitian) :
    G * residual G G.rank = 0 := by
  classical
  have hf := congrArg Prod.snd (state_spectral hG G.rank)
  change residual G G.rank = _ at hf
  rw [hf]
  conv_lhs => lhs; rw [hG.spectral_theorem]
  rw [← map_mul, diagonal_mul_diagonal]
  have hz : (fun i => (hG.eigenvalues i : 𝕜) *
      (spectralPolynomial (fun j => (hG.eigenvalues j : 𝕜))
        (Finset.univ.erase i)).coeff G.rank) = 0 := by
    funext i
    rw [hG.rank_eq_card_non_zero_eigs]
    simpa only [RCLike.ofReal_ne_zero, Pi.zero_apply] using
      spectralPolynomial_erase_top (fun j => (hG.eigenvalues j : 𝕜)) i
  simp only [Function.comp_def] at *
  rw [hz]
  simp

/-- Coefficients above the rank vanish. -/
theorem coeff_eq_zero_of_rank_lt {G : Matrix n n 𝕜} (hG : G.IsHermitian)
    {k : ℕ} (hk : G.rank < k) : coeff G k = 0 := by
  classical
  have hc := congrArg Prod.fst (state_spectral hG k)
  change coeff G k = _ at hc
  rw [hc]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [spectralPolynomial_natDegree]
  simpa only [RCLike.ofReal_ne_zero, ← hG.rank_eq_card_non_zero_eigs] using hk

end Hermitian

end SympyProofs.MoorePenrose.Faddeev
