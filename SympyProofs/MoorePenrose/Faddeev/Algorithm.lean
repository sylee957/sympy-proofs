import SympyProofs.MoorePenrose.Faddeev.Pseudoinverse

/-!
# Executable Faddeev–LeVerrier scan

A single pass retains the last nonzero coefficient and its preceding residual.
The Gram matrix is formed once, and the rectangular numerator is multiplied
only after the scan. There is no pivot selection or matrix-dependent division.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix
open scoped ComplexOrder

section Scan

variable {R n : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq R]
  [Fintype n] [DecidableEq n]

/-- Specification of the last nonzero coefficient up to a given step. -/
def rankUpTo (G : Matrix n n R) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if coeff G (k + 1) = 0 then rankUpTo G k else k + 1

/-- Any nonzero coefficient encountered by the scan is at or below its selected index. -/
theorem le_rankUpTo_of_coeff_ne_zero (G : Matrix n n R) {k l : ℕ}
    (hkl : k ≤ l) (hk : coeff G k ≠ 0) : k ≤ rankUpTo G l := by
  induction l with
  | zero => simpa only [rankUpTo] using hkl
  | succ l ih =>
    by_cases h : coeff G (l + 1) = 0
    · rw [rankUpTo, ite_eq_left h]
      have hne : k ≠ l + 1 := by
        intro heq
        exact hk (heq ▸ h)
      exact ih (by omega)
    · rw [rankUpTo, ite_eq_right h]
      exact hkl

/-- Residual to retain for the final numerator, with the zero-rank case explicit. -/
def numeratorFactor (G : Matrix n n R) : ℕ → Matrix n n R
  | 0 => 0
  | k + 1 => residual G k

/-- State of the executable scan. -/
structure ScanState (n R : Type*) where
  current : Matrix n n R
  rank : ℕ
  coefficient : R
  factor : Matrix n n R

/-- One pass through the Faddeev recurrence, remembering the last nonzero coefficient. -/
def scan (G : Matrix n n R) : ℕ → ScanState n R
  | 0 => ⟨1, 0, 1, 0⟩
  | k + 1 =>
    let prev := scan G k
    let H := G * prev.current
    let e := ((k + 1 : ℚ)⁻¹) • H.trace
    let F := e • 1 - H
    if e = 0 then ⟨F, prev.rank, prev.coefficient, prev.factor⟩
    else ⟨F, k + 1, e, prev.current⟩

/-- The scan computes exactly the recurrence and the specified retained pair. -/
theorem scan_eq (G : Matrix n n R) (k : ℕ) :
    scan G k = ⟨residual G k, rankUpTo G k, coeff G (rankUpTo G k),
      numeratorFactor G (rankUpTo G k)⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scan, ih]
    change (if coeff G (k + 1) = 0 then _ else _) = _
    rw [rankUpTo, residual_succ]
    split_ifs <;> rfl

variable {m : Type*} [Fintype m] [StarRing R]

/-- Compute a polynomial numerator and denominator, detecting rank without pivoting. -/
def computePair (A : Matrix m n R) : Matrix n m R × R :=
  let AH := Aᴴ
  let result := scan (AH * A) (Fintype.card n)
  (result.factor * AH, result.coefficient)

theorem computePair_eq (A : Matrix m n R) :
    computePair A =
      (numerator A (rankUpTo (Aᴴ * A) (Fintype.card n)),
        denominator A (rankUpTo (Aᴴ * A) (Fintype.card n))) := by
  simp only [computePair, scan_eq, denominator]
  cases rankUpTo (Aᴴ * A) (Fintype.card n) <;> simp [numeratorFactor, numerator]

end Scan

section Correctness

variable {𝕜 m n : Type*} [RCLike 𝕜] [DecidableEq 𝕜]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- The last nonzero coefficient detects rank once enough steps have been taken. -/
theorem rankUpTo_eq_rank {G : Matrix n n 𝕜} (hG : G.IsHermitian)
    (k : ℕ) (hk : G.rank ≤ k) : rankUpTo G k = G.rank := by
  induction k with
  | zero =>
    have hr : G.rank = 0 := by omega
    simp [rankUpTo, hr]
  | succ k ih =>
    by_cases hr : G.rank = k + 1
    · rw [rankUpTo, ← hr, ite_eq_right (coeff_rank_ne_zero hG)]
    · have hlt : G.rank < k + 1 := by omega
      rw [rankUpTo, ite_eq_left (coeff_eq_zero_of_rank_lt hG hlt)]
      exact ih (by omega)

/-- The executable scan returns the intrinsic numerator and denominator at the rank. -/
theorem computePair_eq_rank (A : Matrix m n 𝕜) :
    computePair A = (numerator A A.rank, denominator A A.rank) := by
  rw [computePair_eq,
    rankUpTo_eq_rank (Matrix.isHermitian_conjTranspose_mul_self A) _
      (Matrix.rank_le_card_width _), Matrix.rank_conjTranspose_mul_self]

/-- Compute the pseudoinverse by a Faddeev scan followed by one scalar normalization. -/
noncomputable def pseudoinverse (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  let result := computePair A
  result.2⁻¹ • result.1

theorem pseudoinverse_eq (A : Matrix m n 𝕜) :
    pseudoinverse A = pinvAtRank A A.rank := by
  rw [pseudoinverse, computePair_eq_rank]
  rfl

/-- The executable algorithm satisfies all four Moore–Penrose equations. -/
theorem pseudoinverse_isMoorePenrose (A : Matrix m n 𝕜) :
    IsMoorePenrose A (pseudoinverse A) := by
  rw [pseudoinverse_eq]
  exact pinvAtRank_isMoorePenrose A

/-- The final normalization never divides by zero. -/
theorem computePair_denominator_ne_zero (A : Matrix m n 𝕜) :
    (computePair A).2 ≠ 0 := by
  rw [computePair_eq_rank]
  exact denominator_rank_ne_zero A

omit [DecidableEq 𝕜] in
/-- A symbolic scan can be specialized wherever its selected rank is preserved. -/
theorem computePair_specialization {R : Type*} [CommRing R] [Algebra ℚ R]
    [StarRing R] [DecidableEq R] (f : R →ₐ[ℚ] 𝕜)
    (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R)
    (hr : (A.map f).rank = rankUpTo (Aᴴ * A) (Fintype.card n)) :
    f (computePair A).2 ≠ 0 ∧
      IsMoorePenrose (A.map f) ((f (computePair A).2)⁻¹ • (computePair A).1.map f) := by
  rw [computePair_eq]
  exact specialization_correct f hf A _ hr

omit [DecidableEq 𝕜] in
/-- Specialization cannot raise the rank above the index selected symbolically. -/
theorem rank_specialization_le {R : Type*} [CommRing R] [Algebra ℚ R]
    [StarRing R] [DecidableEq R] (f : R →ₐ[ℚ] 𝕜)
    (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) :
    (A.map f).rank ≤ rankUpTo (Aᴴ * A) (Fintype.card n) := by
  apply le_rankUpTo_of_coeff_ne_zero _ (Matrix.rank_le_card_width _)
  change denominator A (A.map f).rank ≠ 0
  intro h
  apply denominator_rank_ne_zero (A.map f)
  rw [denominator_map f hf, h, map_zero]

omit [DecidableEq 𝕜] in
/-- The evaluated output denominator is nonzero exactly where the selected rank is preserved. -/
theorem computePair_specialization_denominator_ne_zero_iff
    {R : Type*} [CommRing R] [Algebra ℚ R] [StarRing R] [DecidableEq R]
    (f : R →ₐ[ℚ] 𝕜) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) :
    f (computePair A).2 ≠ 0 ↔
      (A.map f).rank = rankUpTo (Aᴴ * A) (Fintype.card n) := by
  constructor
  · intro hd
    apply le_antisymm (rank_specialization_le f hf A)
    by_contra h
    apply hd
    rw [computePair_eq]
    change f (denominator A _) = 0
    rw [← denominator_map f hf]
    exact denominator_eq_zero_of_rank_lt _ (by omega)
  · intro hr
    exact (computePair_specialization f hf A hr).1

omit [DecidableEq 𝕜] in
/-- Zeros of the evaluated output denominator are exactly the rank-drop locus. -/
theorem computePair_specialization_denominator_eq_zero_iff
    {R : Type*} [CommRing R] [Algebra ℚ R] [StarRing R] [DecidableEq R]
    (f : R →ₐ[ℚ] 𝕜) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R) :
    f (computePair A).2 = 0 ↔
      (A.map f).rank < rankUpTo (Aᴴ * A) (Fintype.card n) := by
  have hle := rank_specialization_le f hf A
  have hiff := computePair_specialization_denominator_ne_zero_iff f hf A
  constructor
  · intro hd
    have hne : (A.map f).rank ≠ rankUpTo (Aᴴ * A) (Fintype.card n) :=
      fun hr => (hiff.mpr hr) hd
    omega
  · intro hr
    by_contra hd
    have := hiff.mp hd
    omega

omit [DecidableEq 𝕜] in
/-- A nonzero evaluated denominator alone certifies the specialized pseudoinverse. -/
theorem computePair_specialization_of_denominator_ne_zero
    {R : Type*} [CommRing R] [Algebra ℚ R] [StarRing R] [DecidableEq R]
    (f : R →ₐ[ℚ] 𝕜) (hf : ∀ x, f (star x) = star (f x)) (A : Matrix m n R)
    (hd : f (computePair A).2 ≠ 0) :
    IsMoorePenrose (A.map f) ((f (computePair A).2)⁻¹ • (computePair A).1.map f) :=
  (computePair_specialization f hf A
    ((computePair_specialization_denominator_ne_zero_iff f hf A).mp hd)).2

end Correctness

end SympyProofs.MoorePenrose.Faddeev
