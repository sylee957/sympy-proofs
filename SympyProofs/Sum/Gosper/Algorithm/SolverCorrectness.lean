module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm
public import SympyProofs.Sum.Gosper.Backend.Algebra
public import SympyProofs.Sum.Gosper.Backend.FieldExtension
public import SympyProofs.Sum.Gosper.Backend.Matrix
public import SympyProofs.Sum.Gosper.Backend.Vector

/-! A normalized solver over a commutative coefficient algebra, with field-valued correctness. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [DecidableEq K]
variable [DecidablePred (IsInteger ℤ : K → Prop)]
variable (backend : Backend K)

section Algebra

variable {R : Type} [CommRing R] [Algebra K R]

set_option backward.isDefEq.respectTransparency false in
/-- Reduction stays over `K`; the recorded row operations act on the coefficient algebra.
The supplied degree bound fixes all matrix dimensions independently of coefficient values. -/
theorem gosperSolve_eq (hbackend : backend.Valid) (A B : K[X]) (C : R[X])
    (N : ℕ := C.natDegree) :
    gosperSolve backend A B C N =
      let d := degreeBound A B C N
      if d < 0 then none else
        let M := coefficientSystem A B C d.toNat N
        let b := toFn (equationDegree A B C d.toNat N + 1) C
        let r := backend.rref (augmentedIdentity M)
        let coeffs := (r.inverse.map (algebraMap K R)).mulVec b
        some { numerator := B.map (algebraMap K R) *
                 ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (coeffs j)
               denominator := C
               residual := r.residualEntries ((r.rightMatrix.map (algebraMap K R)).mulVec b) } := by
  let d := degreeBound A B C N
  have hM := backend.fill_identity_augmented_eq hbackend (coefficientSystem A B C d.toNat N)
  simp only [Id.run, bind, pure, coefficientSystem, forwardOperator_apply] at hM
  dsimp only [d] at hM
  have htransform {m n : ℕ} (r : RrefResult K m (n + m)) (values : Fin m → R) :=
    r.transform_rhs_algebra_vector_eq values
  simp only [Id.run, bind, pure] at htransform
  have hextract {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) :=
    (backend.rref M).extract_algebra_vector_residual_eq (hbackend.rref_valid M) values
  have hcoefficients {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) := congrArg Prod.fst (hextract M values)
  have hresidual {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) := congrArg Prod.snd (hextract M values)
  simp only [Id.run, bind, pure] at hcoefficients hresidual
  have hsolution {m n : ℕ} (r : RrefResult K m (n + m)) (rhs : Fin m → R) :=
    (r.algebraInverse_mulVec rhs).symm
  have hget {m : ℕ} (values : Fin m → R) (i : Fin m) :
      (Vector.ofFn values)[i.val] = values i := by simp
  simp only [gosperSolve, Id.run, bind, pure, toFn]
  simp only [htransform]
  simp only [hcoefficients, hresidual]
  simp only [hget]
  rw [hM]
  simp only [hsolution]
  rfl

end Algebra

section Field

variable {L : Type} [Field L] [Algebra K L]

private theorem gosperSolve_eq_field (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (N : ℕ) :
    gosperSolve backend A B C N =
      let d := degreeBound A B C N
      if d < 0 then none else
        let M := coefficientSystem A B C d.toNat N
        let b := toFn (equationDegree A B C d.toNat N + 1) C
        let r := (backend.rref (augmentedIdentity M)).map (algebraMap K L)
        let coeffs := r.inverse.mulVec b
        some { numerator := B.map (algebraMap K L) *
                 ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (coeffs j)
               denominator := C
               residual := r.residualEntries (r.rightMatrix.mulVec b) } := by
  rw [gosperSolve_eq backend hbackend A B C N]
  simp only [RrefResult.map_inverse, RrefResult.map_rightMatrix, RrefResult.map_residualEntries]

/-- Vanishing residual entries certify the normalized polynomial equation over `L`. -/
theorem gosperSolve_sound_bounded (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (N : ℕ) (hC : C.natDegree ≤ N)
    (c : Result L) (h : gosperSolve backend A B C N = some c)
    (hzero : ∀ value ∈ c.residual, value = 0) :
    ∃ x : L[X], c.numerator = B.map (algebraMap K L) * x ∧ c.denominator = C ∧
      A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C := by
  classical
  rw [gosperSolve_eq_field backend hbackend] at h
  simp only [← ofFn_eq_sum_monomial] at h
  let d := degreeBound A B C N
  let M := coefficientSystem A B C d.toNat N
  let b := toFn (equationDegree A B C d.toNat N + 1) C
  let r := (backend.rref (augmentedIdentity M)).map (algebraMap K L)
  let coeffs := r.inverse.mulVec b
  let x := ofFn (d.toNat + 1) coeffs
  change (if d < 0 then none else some
    ({ numerator := B.map (algebraMap K L) * x
       denominator := C
       residual := r.residualEntries (r.rightMatrix.mulVec b) } : Result L)) = some c at h
  split_ifs at h with hd
  cases Option.some.inj h
  have hr : r.Valid (augmentedIdentity (M.map (algebraMap K L))) :=
    (backend.rref (augmentedIdentity M)).map_valid_augmentedIdentity M
      (hbackend.rref_valid _) (algebraMap K L)
  have hresidual : r.leftResidual (r.rightMatrix.mulVec b) = 0 :=
    (r.residualEntries_zero_iff hr b).mp hzero
  have hcoeffs : (M.map (algebraMap K L)).mulVec coeffs = b :=
    (r.leftResidual_eq_zero_iff (M.map (algebraMap K L)) hr b).mp hresidual
  refine ⟨x, rfl, rfl, ?_⟩
  exact (coefficientSystem_correct_extension_bounded A B C d.toNat N hC coeffs).mp hcoeffs

/-- The default degree bound certifies the normalized polynomial equation over `L`. -/
theorem gosperSolve_sound (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (c : Result L) (h : gosperSolve backend A B C = some c)
    (hzero : ∀ value ∈ c.residual, value = 0) :
    ∃ x : L[X], c.numerator = B.map (algebraMap K L) * x ∧ c.denominator = C ∧
      A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C :=
  gosperSolve_sound_bounded backend hbackend A B C C.natDegree le_rfl c h hzero

variable [CharZero K]

/-- A polynomial solution over `L` is found using the degree bound and reduction over `K`. -/
theorem gosperSolve_of_solution_bounded (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (N : ℕ) (hbound : C.natDegree ≤ N)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (x : L[X])
    (hx : A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C) :
    ∃ c, gosperSolve backend A B C N = some c ∧ (∀ value ∈ c.residual, value = 0) := by
  classical
  let d := degreeBound A B C N
  let M := coefficientSystem A B C d.toNat N
  let b := toFn (equationDegree A B C d.toNat N + 1) C
  let r := (backend.rref (augmentedIdentity M)).map (algebraMap K L)
  have hr : r.Valid (augmentedIdentity (M.map (algebraMap K L))) :=
    (backend.rref (augmentedIdentity M)).map_valid_augmentedIdentity M
      (hbackend.rref_valid _) (algebraMap K L)
  have hx0 : x ≠ 0 := by
    intro hz
    simp [hz] at hx
    exact hC hx.symm
  have hdeg := solution_degree_le_extension_bounded A B C x N hbound hA hB hx0 hx
  have hd : 0 ≤ d := le_trans (by omega) hdeg
  have hdn : x.natDegree ≤ d.toNat := by omega
  have hm : ∃ c, (M.map (algebraMap K L)).mulVec c = b := by
    refine ⟨toFn (d.toNat + 1) x,
      (coefficientSystem_correct_extension_bounded A B C d.toNat N hbound _).mpr ?_⟩
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
    exact hx
  have hcoeffs : (M.map (algebraMap K L)).mulVec (r.inverse.mulVec b) = b :=
    (r.inverse_solve_iff (M.map (algebraMap K L)) hr b).mpr hm
  have hresidual : r.leftResidual (r.rightMatrix.mulVec b) = 0 :=
    (r.leftResidual_eq_zero_iff (M.map (algebraMap K L)) hr b).mpr hcoeffs
  refine ⟨{ numerator := B.map (algebraMap K L) * ofFn (d.toNat + 1) (r.inverse.mulVec b)
            denominator := C
            residual := r.residualEntries (r.rightMatrix.mulVec b) }, ?_, ?_⟩
  · rw [gosperSolve_eq_field backend hbackend]
    simp only [← ofFn_eq_sum_monomial]
    change (if d < 0 then none else some _) = _
    simp only [not_lt.mpr hd, ↓reduceIte]
    rfl
  · exact (r.residualEntries_zero_iff hr b).mpr hresidual

/-- The default degree bound finds every polynomial solution for nonzero inputs. -/
theorem gosperSolve_of_solution (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (x : L[X])
    (hx : A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C) :
    ∃ c, gosperSolve backend A B C = some c ∧ (∀ value ∈ c.residual, value = 0) :=
  gosperSolve_of_solution_bounded backend hbackend A B C C.natDegree le_rfl hA hB hC x hx

/-- For nonzero `A`, `B`, and `C`, the residual vanishes exactly when the normalized equation
has a polynomial solution over the right-hand-side field. -/
theorem gosperSolve_complete_bounded (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (N : ℕ) (hbound : C.natDegree ≤ N)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (∃ c, gosperSolve backend A B C N = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      ∃ x : L[X], A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C := by
  constructor
  · rintro ⟨c, hc, hzero⟩
    obtain ⟨x, _, _, hx⟩ := gosperSolve_sound_bounded backend hbackend A B C N hbound c hc hzero
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact gosperSolve_of_solution_bounded backend hbackend A B C N hbound hA hB hC x hx

/-- Once an output exists, its residual criterion also covers the zero right-hand side. -/
theorem gosperSolve_result_complete_bounded (hbackend : backend.Valid)
    (A B : K[X]) (C : L[X]) (N : ℕ) (hbound : C.natDegree ≤ N)
    (hA : A ≠ 0) (hB : B ≠ 0) (c : Result L)
    (hrun : gosperSolve backend A B C N = some c) :
    (∀ value ∈ c.residual, value = 0) ↔
      ∃ x : L[X], A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C := by
  classical
  constructor
  · intro hzero
    obtain ⟨x, _, _, hx⟩ := gosperSolve_sound_bounded backend hbackend A B C N hbound c hrun hzero
    exact ⟨x, hx⟩
  · intro hx
    by_cases hC : C = 0
    · subst C
      rw [gosperSolve_eq backend hbackend A B (0 : L[X]) N] at hrun
      simp only [map_zero, Matrix.mulVec_zero] at hrun
      split_ifs at hrun with hd
      cases Option.some.inj hrun
      intro value hv
      obtain ⟨i, p, _, _, he⟩ := (RrefResult.mem_residualEntries _ _ value).mp hv
      exact he.symm
    · obtain ⟨c', hc', hzero⟩ :=
        (gosperSolve_complete_bounded backend hbackend A B C N hbound hA hB hC).mpr hx
      have hc : c = c' := Option.some.inj (hrun.symm.trans hc')
      simpa only [hc] using hzero

/-- The default degree bound gives the same solution criterion. -/
theorem gosperSolve_complete (hbackend : backend.Valid) (A B : K[X]) (C : L[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (∃ c, gosperSolve backend A B C = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      ∃ x : L[X], A.map (algebraMap K L) * taylor 1 x - B.map (algebraMap K L) * x = C :=
  gosperSolve_complete_bounded backend hbackend A B C C.natDegree le_rfl hA hB hC

end Field

end Gosper.Algorithm
