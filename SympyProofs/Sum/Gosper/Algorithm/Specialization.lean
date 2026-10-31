module

public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Rational

/-! Parameter specialization of the normalized solver. The same supplied degree
bound is used on both sides, including when specialization lowers the degree. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Apply a coefficient homomorphism to the candidate and its retained conditions. -/
def Result.map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : Result R) : Result S where
  numerator := r.numerator.map f
  denominator := r.denominator.map f
  residual := r.residual.map f

variable {K R S : Type} [Field K] [DecidableEq K]
variable [DecidablePred (IsInteger ℤ : K → Prop)]
variable [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

omit [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)] in
private theorem matrix_mulVec_map {m n : ℕ} (f : R →ₐ[K] S)
    (M : Matrix (Fin m) (Fin n) K) (b : Fin n → R) :
    f ∘ (M.map (algebraMap K R)).mulVec b =
      (M.map (algebraMap K S)).mulVec (f ∘ b) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Evaluating the retained output is exactly the solver run on evaluated coefficients,
using the same prescribed degree bound. The evaluation need not be injective. -/
theorem gosperSolve_map (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (N : ℕ) (f : R →ₐ[K] S) :
    gosperSolve backend A B (C.map f.toRingHom) N =
      (gosperSolve backend A B C N).map (Result.map f.toRingHom) := by
  have hcoeff {m : ℕ} : toFn m (C.map f.toRingHom) = f ∘ toFn m C := by
    ext i
    simp [toFn]
  have hvec {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) :
      f ∘ (M.map (algebraMap K R)).mulVec (toFn n C) =
        (M.map (algebraMap K S)).mulVec (toFn n (C.map f.toRingHom)) := by
    rw [hcoeff]
    exact matrix_mulVec_map f M _
  simp only [gosperSolve_eq backend hbackend A B (C.map f.toRingHom) N,
    gosperSolve_eq backend hbackend A B C N]
  rw [degreeBound_rhs_eq A B (C.map f.toRingHom) C N]
  split_ifs
  · rfl
  · simp [Result.map, Polynomial.map_sum, Polynomial.map_map,
      RrefResult.residualEntries_map, Function.comp_def]
    let q := backend.rref
      (augmentedIdentity (coefficientSystem A B C (degreeBound A B C N).toNat N))
    constructor
    · apply congrArg (fun p : S[X] => B.map (algebraMap K S) * p)
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (Polynomial.monomial j.val) (congrFun (hvec q.inverse) j).symm
    · exact congrArg (fun v => q.residualEntries v) (hvec q.rightMatrix).symm

section Field

variable {L : Type} [Field L] [Algebra K L]

/-- Vanishing evaluated conditions certify the specialized normalized equation. -/
theorem gosperSolve_specialize_sound (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (N : ℕ) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C N = some r) (hC : C.natDegree ≤ N)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    ∃ x : L[X], r.numerator.map f.toRingHom = B.map (algebraMap K L) * x ∧
      r.denominator.map f.toRingHom = C.map f.toRingHom ∧
      A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x =
        C.map f.toRingHom := by
  have heval : gosperSolve backend A B (C.map f.toRingHom) N =
      some (r.map f.toRingHom) := by
    rw [gosperSolve_map backend hbackend A B C N f, hrun]
    rfl
  apply gosperSolve_sound_bounded backend hbackend A B (C.map f.toRingHom) N
    (Polynomial.natDegree_map_le.trans hC) (r.map f.toRingHom) heval
  simpa [Result.map, Array.mem_map] using hzero

variable [CharZero K]

/-- The evaluated residual detects solvability, including specializations that make
the entire right-hand side zero. -/
theorem gosperSolve_specialize_complete (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (N : ℕ) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C N = some r) (hC : C.natDegree ≤ N)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (∀ value ∈ r.residual, f value = 0) ↔
      ∃ x : L[X], A.map (algebraMap K L) * taylor 1 x -
        B.map (algebraMap K L) * x = C.map f.toRingHom := by
  have heval : gosperSolve backend A B (C.map f.toRingHom) N =
      some (r.map f.toRingHom) := by
    rw [gosperSolve_map backend hbackend A B C N f, hrun]
    rfl
  simpa [Result.map, Array.mem_map] using
    gosperSolve_result_complete_bounded backend hbackend A B (C.map f.toRingHom) N
      (Polynomial.natDegree_map_le.trans hC) hA hB (r.map f.toRingHom) heval

omit [CharZero K] in
/-- The evaluated output is a rational Gosper multiplier for the specialized normal form. -/
theorem gosperSolve_specialize_ratFunc (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (N : ℕ) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C N = some r) (hC : C.natDegree ≤ N)
    (hzero : ∀ value ∈ r.residual, f value = 0)
    (hB : B ≠ 0) (hCeval : C.map f.toRingHom ≠ 0) :
    let a := A.map (algebraMap K L)
    let b := B.map (algebraMap K L)
    let c := C.map f.toRingHom
    let ι := algebraMap L[X] (RatFunc L)
    let multiplier := ι (r.numerator.map f.toRingHom) / ι (r.denominator.map f.toRingHom)
    (ι (a * taylor 1 c) / ι (taylor 1 b * c)) *
        Gosper.rationalShift 1 multiplier - multiplier = 1 := by
  obtain ⟨x, hu, hd, hx⟩ :=
    gosperSolve_specialize_sound backend hbackend A B C N f r hrun hC hzero
  let ι := algebraMap L[X] (RatFunc L)
  let b := B.map (algebraMap K L)
  let c := C.map f.toRingHom
  have hb : b ≠ 0 := by simpa [b] using hB
  have map_ne (p : L[X]) (hp : p ≠ 0) : ι p ≠ 0 := by
    intro hz
    exact hp ((IsFractionRing.injective L[X] (RatFunc L)) (by simpa [ι] using hz))
  have hbnext := map_ne (taylor 1 b) ((taylor_eq_zero _ _).not.mpr hb)
  have hcbase := map_ne c hCeval
  have hcnext := map_ne (taylor 1 c) ((taylor_eq_zero _ _).not.mpr hCeval)
  have he : A.map (algebraMap K L) * taylor 1 (r.numerator.map f.toRingHom) -
      taylor 1 b * r.numerator.map f.toRingHom = taylor 1 b * c := by
    rw [hu, taylor_mul]
    dsimp only [b, c]
    linear_combination taylor 1 (B.map (algebraMap K L)) * hx
  have hm := congrArg ι he
  simp only [map_sub, map_mul] at hm
  dsimp only
  rw [hd]
  simp only [map_div₀, Gosper.rationalShift_polynomial, map_mul]
  change (ι (A.map (algebraMap K L)) * ι (taylor 1 c) /
      (ι (taylor 1 b) * ι c)) *
      (ι (taylor 1 (r.numerator.map f.toRingHom)) / ι (taylor 1 c)) -
      ι (r.numerator.map f.toRingHom) / ι c = 1
  field_simp [hbnext, hcbase, hcnext]
  linear_combination hm

end Field

end Gosper.Algorithm
