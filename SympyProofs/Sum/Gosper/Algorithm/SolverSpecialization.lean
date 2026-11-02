module

public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Rational

/-! Parameter specialization of the retained normalized-solver output.
The source matrix remains valid when evaluation lowers the right-hand-side degree. -/

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

/-- An injective coefficient map preserves all information in a solver result. -/
theorem Result.map_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : Function.Injective (Result.map f) := by
  intro r s h
  cases r
  cases s
  congr 1
  · exact Polynomial.map_injective f hf (congrArg Result.numerator h)
  · exact Polynomial.map_injective f hf (congrArg Result.denominator h)
  · exact (Array.map_inj_right (fun _ _ he => hf he)).mp (congrArg Result.residual h)

variable {K : Type} [Field K]
variable {R : Type} [CommRing R] [Algebra K R]
variable {S : Type} [CommRing S] [Algebra K S]
variable {L : Type} [Field L] [Algebra K L]

private theorem matrix_mulVec_map {m n : ℕ} (f : R →ₐ[K] S)
    (M : Matrix (Fin m) (Fin n) K) (b : Fin n → R) :
    f ∘ (M.map (algebraMap K R)).mulVec b =
      (M.map (algebraMap K S)).mulVec (f ∘ b) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Describe the mapped output using the original coefficient matrix, without rerunning the solver. -/
private theorem gosperSolve_output_map [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) :
    let d := degreeBound A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let q := backend.rref (augmentedIdentity M)
    0 ≤ d ∧ r.map f.toRingHom =
      { numerator := B.map (algebraMap K S) *
          ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val
            ((q.inverse.map (algebraMap K S)).mulVec b j)
        denominator := C.map f.toRingHom
        residual := q.residualEntries ((q.rightMatrix.map (algebraMap K S)).mulVec b) } := by
  have hvec {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) :
      f ∘ (M.map (algebraMap K R)).mulVec (toFn n C) =
        (M.map (algebraMap K S)).mulVec (toFn n (C.map f.toRingHom)) := by
    have hcoeff : toFn n (C.map f.toRingHom) = f ∘ toFn n C := by
      ext i
      simp [toFn]
    rw [hcoeff]
    exact matrix_mulVec_map f M _
  rw [gosperSolve_eq backend hbackend] at hrun
  dsimp only at hrun ⊢
  split_ifs at hrun with hd
  cases Option.some.inj hrun
  refine ⟨not_lt.mp hd, ?_⟩
  simp [Result.map, Polynomial.map_sum, Polynomial.map_map,
    RrefResult.residualEntries_map, Function.comp_def]
  let q := backend.rref (augmentedIdentity
    (coefficientSystem A B C (degreeBound A B C).toNat))
  constructor
  · apply congrArg (fun p : S[X] => B.map (algebraMap K S) * p)
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (Polynomial.monomial j.val) (congrFun (hvec q.inverse) j)
  · exact congrArg (fun v => q.residualEntries v) (hvec q.rightMatrix)

set_option backward.isDefEq.respectTransparency false in
/-- Rerunning the solver commutes with evaluation when the right-hand-side degree is
preserved. The direct output-specialization theorems below also cover degree drops. -/
theorem gosperSolve_map [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S)
    (hdegree : (C.map f.toRingHom).natDegree = C.natDegree) :
    gosperSolve backend A B (C.map f.toRingHom) =
      (gosperSolve backend A B C).map (Result.map f.toRingHom) := by
  have hvec {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) :
      f ∘ (M.map (algebraMap K R)).mulVec (toFn n C) =
        (M.map (algebraMap K S)).mulVec (toFn n (C.map f.toRingHom)) := by
    have hcoeff : toFn n (C.map f.toRingHom) = f ∘ toFn n C := by
      ext i
      simp [toFn]
    rw [hcoeff]
    exact matrix_mulVec_map f M _
  simp only [gosperSolve_eq backend hbackend A B (C.map f.toRingHom),
    gosperSolve_eq backend hbackend A B C]
  rw [degreeBound_rhs_eq A B (C.map f.toRingHom) C hdegree]
  delta coefficientSystem
  rw [hdegree]
  split_ifs
  · rfl
  · simp [Result.map, Polynomial.map_sum, Polynomial.map_map,
      RrefResult.residualEntries_map, Function.comp_def]
    let q := backend.rref (augmentedIdentity
      (fun (i : Fin (max C.natDegree
          (max A.natDegree B.natDegree + (degreeBound A B C).toNat) + 1))
        (j : Fin ((degreeBound A B C).toNat + 1)) =>
        (A * (X + 1) ^ j.val).coeff i.val - (B * X ^ j.val).coeff i.val))
    constructor
    · apply congrArg (fun p : S[X] => B.map (algebraMap K S) * p)
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (Polynomial.monomial j.val) (congrFun (hvec q.inverse) j).symm
    · exact congrArg (fun v => q.residualEntries v) (hvec q.rightMatrix).symm

/-- A solver output over an injective coefficient extension determines the source output. -/
theorem gosperSolve_of_map [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (i : R →ₐ[K] L) (hi : Function.Injective i)
    (r : Result R)
    (hrun : gosperSolve backend A B (C.map i.toRingHom) = some (r.map i.toRingHom)) :
    gosperSolve backend A B C = some r := by
  rw [gosperSolve_map backend hbackend A B C i
    (Polynomial.natDegree_map_eq_of_injective hi C)] at hrun
  cases hsource : gosperSolve backend A B C with
  | none => simp [hsource] at hrun
  | some s =>
      have he : s.map i.toRingHom = r.map i.toRingHom := by simpa [hsource] using hrun
      exact congrArg some (Result.map_injective i.toRingHom hi he)

/-- The solver retains its right-hand side as the candidate denominator. -/
theorem gosperSolve_denominator [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) : r.denominator = C := by
  rw [gosperSolve_eq backend hbackend A B C] at hrun
  dsimp only at hrun
  split_ifs at hrun
  cases Option.some.inj hrun
  rfl

/-- Vanishing evaluated conditions certify the specialized normalized equation.
No injectivity or preservation of the right-hand-side degree is required. -/
theorem gosperSolve_specialize_sound [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C = some r)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    ∃ x : L[X], r.numerator.map f.toRingHom = B.map (algebraMap K L) * x ∧
      r.denominator.map f.toRingHom = C.map f.toRingHom ∧
      A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x =
        C.map f.toRingHom := by
  classical
  obtain ⟨hd, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun
  let d := degreeBound A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q := (backend.rref (augmentedIdentity M)).map (algebraMap K L)
  have hq : q.Valid (augmentedIdentity (M.map (algebraMap K L))) :=
    (backend.rref (augmentedIdentity M)).map_valid_augmentedIdentity M
      (hbackend.rref_valid _) (algebraMap K L)
  have hz : ∀ value ∈ (r.map f.toRingHom).residual, value = 0 := by
    simpa [Result.map, Array.mem_map] using hzero
  rw [he] at hz
  have hres : q.leftResidual (q.rightMatrix.mulVec b) = 0 := by
    apply (q.residualEntries_zero_iff hq b).mp
    simpa only [q, RrefResult.map_residualEntries, RrefResult.map_rightMatrix] using hz
  have hcoeffs : (M.map (algebraMap K L)).mulVec (q.inverse.mulVec b) = b :=
    (q.leftResidual_eq_zero_iff (M.map (algebraMap K L)) hq b).mp hres
  refine ⟨ofFn (d.toNat + 1) (q.inverse.mulVec b), ?_, ?_, ?_⟩
  · have hu := congrArg Result.numerator he
    simpa only [Result.map, q, RrefResult.map_inverse, ofFn_eq_sum_monomial] using hu
  · exact congrArg Result.denominator he
  · exact (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
      d.toNat C.natDegree Polynomial.natDegree_map_le (q.inverse.mulVec b)).mp hcoeffs

/-- The retained output's evaluated residual detects solvability, including degree
drops and specializations that make the entire right-hand side zero. -/
theorem gosperSolve_specialize_complete [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)] [CharZero K]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) (hA : A ≠ 0) (hB : B ≠ 0) :
    (∀ value ∈ r.residual, f value = 0) ↔
      ∃ x : L[X], A.map (algebraMap K L) * taylor 1 x -
        B.map (algebraMap K L) * x = C.map f.toRingHom := by
  classical
  constructor
  · intro hzero
    obtain ⟨x, _, _, hx⟩ :=
      gosperSolve_specialize_sound backend hbackend A B C f r hrun hzero
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hd, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun
    let d := degreeBound A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let q := (backend.rref (augmentedIdentity M)).map (algebraMap K L)
    have hq : q.Valid (augmentedIdentity (M.map (algebraMap K L))) :=
      (backend.rref (augmentedIdentity M)).map_valid_augmentedIdentity M
        (hbackend.rref_valid _) (algebraMap K L)
    have hdn : x.natDegree ≤ d.toNat := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hdeg := solution_degree_le_extension_bounded A B C (C.map f.toRingHom) x
          Polynomial.natDegree_map_le hA hB hx0 hx
        omega
    have hm : ∃ c, (M.map (algebraMap K L)).mulVec c = b := by
      refine ⟨toFn (d.toNat + 1) x,
        (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
          d.toNat C.natDegree Polynomial.natDegree_map_le _).mpr ?_⟩
      rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
      exact hx
    have hcoeffs : (M.map (algebraMap K L)).mulVec (q.inverse.mulVec b) = b :=
      (q.inverse_solve_iff (M.map (algebraMap K L)) hq b).mpr hm
    have hres := (q.leftResidual_eq_zero_iff (M.map (algebraMap K L)) hq b).mpr hcoeffs
    have hzq := (q.residualEntries_zero_iff hq b).mpr hres
    have hz : ∀ value ∈ (r.map f.toRingHom).residual, value = 0 := by
      rw [he]
      simpa only [q, RrefResult.map_residualEntries, RrefResult.map_rightMatrix] using hzq
    simpa [Result.map, Array.mem_map] using hz

/-- The evaluated output is a rational Gosper multiplier for the specialized normal form. -/
theorem gosperSolve_specialize_ratFunc [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] L) (r : Result R)
    (hrun : gosperSolve backend A B C = some r)
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
    gosperSolve_specialize_sound backend hbackend A B C f r hrun hzero
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

end Gosper.Algorithm
