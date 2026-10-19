import SympyProofs.MoorePenrose.Faddeev.Spectrum

/-!
# Moore–Penrose inverse from Faddeev–LeVerrier

For `G = Aᴴ * A` and rank `r > 0`, the numerator is `F_{r-1} * Aᴴ`
and the denominator is `e_r`. At rank zero the pair is `(0, 1)`.
The denominator is nonzero at every matrix of the specified rank.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix
open scoped ComplexOrder

section PolynomialPair

variable {R m n : Type*} [CommRing R] [Algebra ℚ R] [StarRing R]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- The polynomial numerator; no input-dependent division is used. -/
def numerator (A : Matrix m n R) : ℕ → Matrix n m R
  | 0 => 0
  | k + 1 => residual (Aᴴ * A) k * Aᴴ

/-- The intrinsic denominator, calculated by the trace recurrence. -/
def denominator (A : Matrix m n R) (r : ℕ) : R := coeff (Aᴴ * A) r

@[simp] theorem numerator_zero_rank (A : Matrix m n R) : numerator A 0 = 0 := rfl
@[simp] theorem denominator_zero_rank (A : Matrix m n R) : denominator A 0 = 1 := rfl

theorem numerator_succ (A : Matrix m n R) (k : ℕ) :
    numerator A (k + 1) = residual (Aᴴ * A) k * Aᴴ := rfl

omit [Fintype n] [DecidableEq n] in
/-- Evaluation preserving conjugation commutes with the Gram matrix. -/
private theorem gram_map {S : Type*} [CommRing S] [Algebra ℚ S] [StarRing S]
    (f : R →ₐ[ℚ] S) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) :
    (A.map f)ᴴ * A.map f = (Aᴴ * A).map f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    map_sum, map_mul, hf]

/-- The denominator can be computed symbolically before evaluating parameters. -/
theorem denominator_map {S : Type*} [CommRing S] [Algebra ℚ S] [StarRing S]
    (f : R →ₐ[ℚ] S) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) (r : ℕ) :
    denominator (A.map f) r = f (denominator A r) := by
  unfold denominator
  rw [gram_map f hf]
  exact congrArg Prod.fst (state_map f (Aᴴ * A) r)

/-- The numerator can be computed symbolically before evaluating parameters. -/
theorem numerator_map {S : Type*} [CommRing S] [Algebra ℚ S] [StarRing S]
    (f : R →ₐ[ℚ] S) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) (r : ℕ) :
    numerator (A.map f) r = (numerator A r).map f := by
  cases r with
  | zero => simp
  | succ k =>
    rw [numerator_succ, numerator_succ, gram_map f hf]
    have hF := congrArg Prod.snd (state_map f (Aᴴ * A) k)
    change residual ((Aᴴ * A).map f) k = (residual (Aᴴ * A) k).map f at hF
    rw [hF]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
      map_sum, map_mul, hf]

end PolynomialPair

section Correctness

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- Normalize the Faddeev pair at a supplied rank. -/
noncomputable def pinvAtRank (A : Matrix m n 𝕜) (r : ℕ) : Matrix n m 𝕜 :=
  (denominator A r)⁻¹ • numerator A r

/-- The only input-dependent denominator is nonzero on the entire rank stratum. -/
theorem denominator_rank_ne_zero (A : Matrix m n 𝕜) :
    denominator A A.rank ≠ 0 := by
  unfold denominator
  rw [← Matrix.rank_conjTranspose_mul_self A]
  exact coeff_rank_ne_zero (Matrix.isHermitian_conjTranspose_mul_self A)

private theorem pinvAtRank_succ_isMoorePenrose (A : Matrix m n 𝕜) (k : ℕ)
    (hr : A.rank = k + 1) : IsMoorePenrose A (pinvAtRank A (k + 1)) := by
  let G := Aᴴ * A
  let F := residual G k
  let e := coeff G (k + 1)
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hF : F.IsHermitian := (state_hermitian hG k).2
  have he : star e = e := (state_hermitian hG (k + 1)).1
  have he0 : e ≠ 0 := by
    simpa only [e, denominator, hr] using denominator_rank_ne_zero A
  have hGr : G.rank = k + 1 := (Matrix.rank_conjTranspose_mul_self A).trans hr
  have ht : G * residual G (k + 1) = 0 := by
    simpa only [hGr] using mul_residual_rank hG
  have ha : A * residual G (k + 1) = 0 :=
    (Matrix.conjTranspose_mul_self_mul_eq_zero A _).mp ht
  have hat : residual G (k + 1) * Aᴴ = 0 := by
    have := congrArg Matrix.conjTranspose ha
    simpa only [Matrix.conjTranspose_mul, (state_hermitian hG (k + 1)).2.eq,
      Matrix.conjTranspose_zero] using this
  have hGF : G * F * Aᴴ = e • Aᴴ := by
    rw [residual_succ, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hat
    exact (sub_eq_zero.mp hat).symm
  have hAFG : A * F * G = e • A := by
    have := congrArg Matrix.conjTranspose hGF
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hF.eq, hG.eq, Matrix.conjTranspose_smul, he, Matrix.mul_assoc] using this
  change IsMoorePenrose A (e⁻¹ • (F * Aᴴ))
  constructor
  · calc
      A * (e⁻¹ • (F * Aᴴ)) * A = e⁻¹ • (A * F * G) := by
        simp only [G, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = A := by rw [hAFG, smul_smul, inv_mul_cancel₀ he0, one_smul]
  · calc
      (e⁻¹ • (F * Aᴴ)) * A * (e⁻¹ • (F * Aᴴ)) =
          e⁻¹ • (e⁻¹ • (F * (G * F * Aᴴ))) := by
        simp only [G, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = e⁻¹ • (F * Aᴴ) := by
        rw [hGF, Matrix.mul_smul]
        simp only [smul_smul, inv_mul_cancel₀ he0, mul_one]
  · simp only [Matrix.mul_smul, Matrix.conjTranspose_smul, star_inv₀, he,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hF.eq,
      Matrix.mul_assoc]
  · simp only [Matrix.smul_mul, Matrix.conjTranspose_smul, star_inv₀, he,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hF.eq]
    congr 1
    simpa only [G, Matrix.mul_assoc] using residual_commute G k

/-- Faddeev–LeVerrier computes the Moore–Penrose inverse for every finite matrix. -/
theorem pinvAtRank_isMoorePenrose (A : Matrix m n 𝕜) :
    IsMoorePenrose A (pinvAtRank A A.rank) := by
  cases hr : A.rank with
  | zero =>
    have hGram : Aᴴ * A = 0 := by
      simpa only [Matrix.rank_conjTranspose_mul_self, hr, residual_zero, Matrix.mul_one]
        using mul_residual_rank (Matrix.isHermitian_conjTranspose_mul_self A)
    have hA : A = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hGram
    subst A
    simpa [pinvAtRank] using (IsMoorePenrose.zero (m := m) (n := n) (𝕜 := 𝕜))
  | succ k => exact pinvAtRank_succ_isMoorePenrose A k hr

/-- The resulting pseudoinverse is unique. -/
theorem isMoorePenrose_iff (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    IsMoorePenrose A B ↔ B = pinvAtRank A A.rank :=
  ⟨fun h => h.unique (pinvAtRank_isMoorePenrose A),
    fun h => h ▸ pinvAtRank_isMoorePenrose A⟩

/-- Specializing a matrix family at any point of the same rank is safe. -/
theorem no_spurious_poles {T : Type*} (A : T → Matrix m n 𝕜) (r : ℕ)
    (x : T) (hr : (A x).rank = r) :
    denominator (A x) r ≠ 0 ∧ IsMoorePenrose (A x) (pinvAtRank (A x) r) := by
  subst r
  exact ⟨denominator_rank_ne_zero (A x), pinvAtRank_isMoorePenrose (A x)⟩

/-- A higher-rank formula has zero denominator at an actual rank drop. -/
theorem denominator_eq_zero_of_rank_lt (A : Matrix m n 𝕜) {r : ℕ} (hr : A.rank < r) :
    denominator A r = 0 := by
  apply coeff_eq_zero_of_rank_lt (Matrix.isHermitian_conjTranspose_mul_self A)
  simpa only [Matrix.rank_conjTranspose_mul_self] using hr

/-- The symbolically computed polynomial pair specializes correctly wherever rank is `r`. -/
theorem specialization_correct {R : Type*} [CommRing R] [Algebra ℚ R] [StarRing R]
    (f : R →ₐ[ℚ] 𝕜) (hf : ∀ x, f (star x) = star (f x))
    (A : Matrix m n R) (r : ℕ) (hr : (A.map f).rank = r) :
    f (denominator A r) ≠ 0 ∧
      IsMoorePenrose (A.map f) ((f (denominator A r))⁻¹ • (numerator A r).map f) := by
  rw [← denominator_map f hf, ← numerator_map f hf, ← hr]
  exact ⟨denominator_rank_ne_zero (A.map f), pinvAtRank_isMoorePenrose (A.map f)⟩

end Correctness

end SympyProofs.MoorePenrose.Faddeev
