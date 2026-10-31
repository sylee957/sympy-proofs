module

public import SympyProofs.Sum.Gosper.Backend.Inverse

/-! A rational generalized inverse can be applied to parameter-valued right-hand sides.
Elimination is confined to the rational matrix. Neither constructing a candidate nor
specializing it requires decidable equality on the parameter algebra. -/

@[expose] public section

namespace Gosper.Algorithm

variable {m n : ℕ}

/-- The generalized-inverse identity survives any change of coefficient semiring. -/
theorem generalizedInverse_map {K R : Type*} [Semiring K] [Semiring R]
    (A : Matrix (Fin m) (Fin n) K) (U : Matrix (Fin n) (Fin m) K)
    (h : A * U * A = A) (f : K →+* R) :
    A.map f * U.map f * A.map f = A.map f := by
  simpa only [Matrix.map_mul] using congrArg (fun M => M.map f) h

/-- Applying a generalized inverse succeeds exactly for right-hand sides in the image. -/
theorem generalizedInverse_solve_iff {R : Type*} [Semiring R]
    (A : Matrix (Fin m) (Fin n) R) (U : Matrix (Fin n) (Fin m) R)
    (h : A * U * A = A) (b : Fin m → R) :
    A.mulVec (U.mulVec b) = b ↔ ∃ x, A.mulVec x = b := by
  constructor
  · exact fun hb => ⟨U.mulVec b, hb⟩
  · rintro ⟨x, rfl⟩
    simpa only [← Matrix.mulVec_mulVec] using congrArg (fun M => M.mulVec x) h

/-- A generalized inverse computed in `K` solves every attainable right-hand side in `R`. -/
theorem generalizedInverse_map_solve_iff {K R : Type*} [Semiring K] [Semiring R]
    (A : Matrix (Fin m) (Fin n) K) (U : Matrix (Fin n) (Fin m) K)
    (h : A * U * A = A) (f : K →+* R) (b : Fin m → R) :
    (A.map f).mulVec ((U.map f).mulVec b) = b ↔
      ∃ x, (A.map f).mulVec x = b :=
  generalizedInverse_solve_iff _ _ (generalizedInverse_map A U h f) b

section Rational

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

/-- RREF is run over `ℚ` once; its inverse solves all attainable parameter-valued right-hand sides.
No equality decision or field structure is required on the parameter algebra. -/
theorem inverseRref_map_solve_iff (rref : RrefOperation ℚ)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) ℚ), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → R) :
    (A.map (algebraMap ℚ R)).mulVec
        (((inverseRref rref A).map (algebraMap ℚ R)).mulVec b) = b ↔
      ∃ x, (A.map (algebraMap ℚ R)).mulVec x = b :=
  generalizedInverse_map_solve_iff A _ (inverseRref_mul rref valid A) (algebraMap ℚ R) b

/-- Apply the prepared rational inverse using only addition and rational scalar multiplication. -/
def rationalInverseCandidate (U : Matrix (Fin n) (Fin m) ℚ) (b : Fin m → R) : Fin n → R :=
  (U.map (algebraMap ℚ R)).mulVec b

/-- The residual is retained as an algebra-valued vector, without an equality test. -/
def rationalInverseResidual (A : Matrix (Fin m) (Fin n) ℚ)
    (U : Matrix (Fin n) (Fin m) ℚ) (b : Fin m → R) : Fin m → R :=
  (A.map (algebraMap ℚ R)).mulVec (rationalInverseCandidate U b) - b

/-- A zero residual characterizes solvability over the parameter algebra. -/
theorem rationalInverseResidual_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℚ)
    (U : Matrix (Fin n) (Fin m) ℚ) (h : A * U * A = A) (b : Fin m → R) :
    rationalInverseResidual A U b = 0 ↔
      ∃ x, (A.map (algebraMap ℚ R)).mulVec x = b := by
  rw [rationalInverseResidual, sub_eq_zero]
  exact generalizedInverse_map_solve_iff A U h (algebraMap ℚ R) b

/-- The residual of the inverse prepared by rational RREF completely detects solvability. -/
theorem inverseRref_map_residual_eq_zero_iff (rref : RrefOperation ℚ)
    (valid : ∀ {m n} (A : Matrix (Fin m) (Fin n) ℚ), (rref A).Valid A)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → R) :
    rationalInverseResidual A (inverseRref rref A) b = 0 ↔
      ∃ x, (A.map (algebraMap ℚ R)).mulVec x = b :=
  rationalInverseResidual_eq_zero_iff A _ (inverseRref_mul rref valid A) b

/-- Specializing parameters commutes with multiplication by a rational matrix. -/
theorem rationalMatrix_mulVec_map (f : R →ₐ[ℚ] S)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin n → R) :
    f ∘ (A.map (algebraMap ℚ R)).mulVec b =
      (A.map (algebraMap ℚ S)).mulVec (f ∘ b) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- The prepared candidate specializes without rerunning elimination. -/
theorem rationalInverseCandidate_map (f : R →ₐ[ℚ] S)
    (U : Matrix (Fin n) (Fin m) ℚ) (b : Fin m → R) :
    f ∘ rationalInverseCandidate U b = rationalInverseCandidate U (f ∘ b) :=
  rationalMatrix_mulVec_map f U b

/-- Residuals also specialize, including when a nonzero symbolic residual vanishes at a parameter. -/
theorem rationalInverseResidual_map (f : R →ₐ[ℚ] S)
    (A : Matrix (Fin m) (Fin n) ℚ) (U : Matrix (Fin n) (Fin m) ℚ) (b : Fin m → R) :
    f ∘ rationalInverseResidual A U b = rationalInverseResidual A U (f ∘ b) := by
  have h := rationalMatrix_mulVec_map f A (rationalInverseCandidate U b)
  rw [rationalInverseCandidate_map] at h
  ext i
  simpa only [rationalInverseResidual, Function.comp_apply, Pi.sub_apply, map_sub]
    using congrArg (fun v => v i - f (b i)) h

/-- Evaluating the retained residual detects solvability at the specialized parameter. -/
theorem rationalInverseResidual_map_eq_zero_iff (f : R →ₐ[ℚ] S)
    (A : Matrix (Fin m) (Fin n) ℚ) (U : Matrix (Fin n) (Fin m) ℚ)
    (h : A * U * A = A) (b : Fin m → R) :
    f ∘ rationalInverseResidual A U b = 0 ↔
      ∃ x, (A.map (algebraMap ℚ S)).mulVec x = f ∘ b := by
  rw [rationalInverseResidual_map]
  exact rationalInverseResidual_eq_zero_iff A U h (f ∘ b)

end Rational

end Gosper.Algorithm
