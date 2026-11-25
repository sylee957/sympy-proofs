module

public import SympyProofs.LinearAlgebra.Eigenvectors.Orthogonalization
public import SympyProofs.LinearAlgebra.MoorePenrose.Basic

/-! # Gram-matrix pseudoinverses from unnormalized eigenvectors -/

@[expose] public section

noncomputable section
namespace SympyProofs.MoorePenrose

open Matrix Diagonalization

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- Reciprocal eigenvalues and reciprocal squared column lengths. A zero eigenvalue
contributes zero by total division. -/
def gramPseudoinverse (P : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  let Q := orthogonalizeColumns P
  Q * diagonal (fun i => (d i)⁻¹ / (star (Q.col i) ⬝ᵥ Q.col i)) * Qᴴ

theorem gramPseudoinverse_isMoorePenrose {G P : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜}
    (hG : G.IsHermitian) (h : IsDiagonalization G P d) :
    IsMoorePenrose G (gramPseudoinverse P d) := by
  let Q := orthogonalizeColumns P
  have hQ := h.orthogonalizeColumns hG
  let len := fun i => star (Q.col i) ⬝ᵥ Q.col i
  let spectral := fun f : Fin n → 𝕜 => Q * diagonal f * Q⁻¹
  have weight (f : Fin n → 𝕜) : spectral f = Q * diagonal (fun i => f i / len i) * Qᴴ := by
    dsimp only [spectral]
    rw [inv_of_orthogonal_columns hQ.1 (fun _ _ => orthogonalizeColumns_orthogonal P),
      ← mul_assoc, mul_assoc Q, diagonal_mul_diagonal]
    simp only [len, div_eq_mul_inv, Q]
  have prod (f g : Fin n → 𝕜) : spectral f * spectral g = spectral (f * g) := by
    simp only [spectral, mul_assoc, Q.nonsing_inv_mul_cancel_left _ (isUnit_iff_ne_zero.mpr hQ.1)]
    rw [← mul_assoc (diagonal f), diagonal_mul_diagonal]
    rfl
  have proj : (spectral (d * d⁻¹)).IsHermitian := by
    rw [weight]
    apply isHermitian_mul_mul_conjTranspose Q (isHermitian_diagonal_iff.mpr ?_)
    intro i
    have hl : star (len i) = len i := (star_dotProduct (Q.col i) (Q.col i)).symm
    by_cases hi : d i = 0 <;> simp [isSelfAdjoint_iff, hi, hl]
  have formula : spectral d⁻¹ = gramPseudoinverse P d := weight _
  rw [← formula, show G = spectral d from hQ.2]
  constructor
  · simp only [prod]
    congr 1
    funext i
    simp
  · simp only [prod]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  · rw [prod]
    exact proj
  · rw [prod, mul_comm]
    exact proj

private theorem gram_inverse_hermitian {G B : Matrix (Fin n) (Fin n) 𝕜}
    (hG : G.IsHermitian) (hB : IsMoorePenrose G B) : B.IsHermitian :=
  IsMoorePenrose.unique (hG.eq ▸ hB.conjTranspose) hB

open scoped ComplexOrder in
private theorem right_gram_inverse {A : Matrix (Fin m) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsMoorePenrose (Aᴴ * A) B) : IsMoorePenrose A (B * Aᴴ) := by
  have hb := (gram_inverse_hermitian (isHermitian_conjTranspose_mul_self A) h).eq
  have hleft : A * (B * (Aᴴ * A) - 1) = 0 := by
    apply (conjTranspose_mul_self_mul_eq_zero A _).mp
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h.left, mul_one, sub_self]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← sub_eq_zero]
    simpa only [Matrix.mul_sub, Matrix.mul_one] using hleft
  · simpa only [Matrix.mul_assoc] using congrArg (· * Aᴴ) h.right
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, hb, Matrix.mul_assoc]
  · simpa only [Matrix.mul_assoc] using h.right_hermitian

/-- For G = AᴴA, the corrected pseudoinverse of A is G⁺Aᴴ. -/
theorem right_gramPseudoinverse_isMoorePenrose {A : Matrix (Fin m) (Fin n) 𝕜}
    {P : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜} (h : IsDiagonalization (Aᴴ * A) P d) :
    IsMoorePenrose A (gramPseudoinverse P d * Aᴴ) :=
  right_gram_inverse (gramPseudoinverse_isMoorePenrose (isHermitian_conjTranspose_mul_self A) h)

/-- For G = AAᴴ, the corrected pseudoinverse of A is AᴴG⁺. -/
theorem left_gramPseudoinverse_isMoorePenrose {A : Matrix (Fin m) (Fin n) 𝕜}
    {P : Matrix (Fin m) (Fin m) 𝕜} {d : Fin m → 𝕜} (h : IsDiagonalization (A * Aᴴ) P d) :
    IsMoorePenrose A (Aᴴ * gramPseudoinverse P d) := by
  have hG := isHermitian_mul_conjTranspose_self A
  have hb := gram_inverse_hermitian hG (gramPseudoinverse_isMoorePenrose hG h)
  have h' := right_gramPseudoinverse_isMoorePenrose (A := Aᴴ) (by simpa using h)
  simpa only [conjTranspose_conjTranspose, conjTranspose_mul, hb.eq] using h'.conjTranspose

end SympyProofs.MoorePenrose
