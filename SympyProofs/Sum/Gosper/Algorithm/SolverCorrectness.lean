module

public import SympyProofs.Sum.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Sum.Gosper.Algorithm.Degree
public import SympyProofs.Sum.Gosper.Backend.LinearAlgebra

/-! Fraction-free normalized solving and specialization of its polynomial remainder. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial
attribute [local instance 2000] Ring.toIntAlgebra

/-- An injective coefficient map preserves all information in a solver result. -/
theorem Result.map_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : Function.Injective (Result.map f) := by
  intro r s h
  cases r
  cases s
  congr 1
  · exact Polynomial.map_injective f hf (congrArg Result.numerator h)
  · exact Polynomial.map_injective f hf (congrArg Result.denominator h)
  · exact Polynomial.map_injective f hf (congrArg Result.residual h)

variable {K : Type} [CommRing K]
variable {R S : Type} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
variable {E : Type} [Field E] [Algebra K E]

private theorem matrix_mulVec_map {m n : ℕ} (f : R →ₐ[K] S)
    (M : Matrix (Fin m) (Fin n) K) (b : Fin n → R) :
    f ∘ (M.map (algebraMap K R)).mulVec b =
      (M.map (algebraMap K S)).mulVec (f ∘ b) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

private theorem rawLeftSolution_map {m n : ℕ} (q : RrefResult K m (n + m))
    (f : R →ₐ[K] S) (values : Fin m → R) :
    f ∘ q.rawLeftSolution values = q.rawLeftSolution (f ∘ values) := by
  ext j
  simp [RrefResult.rawLeftSolution, map_sum, apply_ite]

variable [IsDomain K] [DecidableEq K]

set_option backward.isDefEq.respectTransparency false in
/-- The imperative solver records raw pivot values and keeps the common denominator. -/
theorem gosperSolve_eq (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) :
    gosperSolve backend A B C =
      let d := degreeBound backend A B C
      if d < 0 then
        { numerator := 0, denominator := C
          residual := C }
      else
        let M := coefficientSystem A B C d.toNat
        let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1) C
        let r := backend.rref (augmentedIdentity M)
        let y := (r.rightMatrix.map (algebraMap K R)).mulVec b
        { numerator := B.map (algebraMap K R) *
            ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (r.rawLeftSolution y j)
          denominator := Polynomial.C (algebraMap K R r.denominator) * C
          residual := Polynomial.C (algebraMap K R r.denominator) * C -
            (A.map (algebraMap K R) * taylor 1
                (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (r.rawLeftSolution y j)) -
              B.map (algebraMap K R) *
                ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (r.rawLeftSolution y j)) } := by
  let d := degreeBound backend A B C
  have hM := backend.fill_identity_augmented_eq hbackend (coefficientSystem A B C d.toNat)
  simp only [Id.run, bind, pure, coefficientSystem, forwardOperator_apply] at hM
  dsimp only [d] at hM
  have htransform {m n : ℕ} (r : RrefResult K m (n + m)) (values : Fin m → R) :=
    r.transform_rhs_ring_vector_eq values
  simp only [Id.run, bind, pure] at htransform
  have hcoefficients {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) :=
    (backend.rref M).extract_raw_coefficients_eq (hbackend.rref_valid M).ordered values
  simp only [Id.run, bind, pure] at hcoefficients
  have hget {m : ℕ} (values : Fin m → R) (i : Fin m) :
      (Vector.ofFn values)[i.val] = values i := by simp
  simp only [gosperSolve, Id.run, bind, pure, toFn]
  simp only [htransform, hcoefficients, hget]
  rw [hM]
  rfl

/-- A negative degree bound returns the complete right-hand side as a remainder. -/
theorem gosperSolve_of_degreeBound_neg (backend : LinearBackend K)
    (A B : K[X]) (C : R[X]) (hd : degreeBound backend A B C < 0) :
    gosperSolve backend A B C =
      { numerator := 0, denominator := C
        residual := C } := by
  simp [gosperSolve, hd]

/-- Every returned denominator is the supplied right-hand side multiplied by a nonzero
constant from the coefficient domain. -/
theorem gosperSolve_denominator (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (r : Result R)
    (hrun : gosperSolve backend A B C = r) :
    ∃ δ : K, δ ≠ 0 ∧ r.denominator = Polynomial.C (algebraMap K R δ) * C := by
  rw [gosperSolve_eq backend hbackend A B C] at hrun
  dsimp only at hrun
  split_ifs at hrun with hd
  · cases hrun.symm
    exact ⟨1, one_ne_zero, by simp⟩
  cases hrun.symm
  refine ⟨_, ?_, rfl⟩
  have hn := (hbackend.rref_valid (augmentedIdentity
    (coefficientSystem A B C (degreeBound backend A B C).toNat))).denominator_ne_zero
  intro hz
  exact hn (by simp [RrefResult.map, hz])

/-- Every run supplies a polynomial reduction, whether or not the
polynomial remainder vanishes. -/
theorem gosperSolve_reduction_data (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (r : Result R)
    (hrun : gosperSolve backend A B C = r) :
    ∃ δ : K, δ ≠ 0 ∧ ∃ x : R[X],
      r.numerator = B.map (algebraMap K R) * x ∧
      r.denominator = Polynomial.C (algebraMap K R δ) * C ∧
      r.residual = r.denominator -
        (A.map (algebraMap K R) * taylor 1 x - B.map (algebraMap K R) * x) := by
  rw [gosperSolve_eq backend hbackend A B C] at hrun
  dsimp only at hrun
  split_ifs at hrun with hd
  · cases hrun.symm
    exact ⟨1, one_ne_zero, 0, by simp⟩
  cases hrun.symm
  refine ⟨_, ?_, _, rfl, rfl, rfl⟩
  have hn := (hbackend.rref_valid (augmentedIdentity
    (coefficientSystem A B C (degreeBound backend A B C).toNat))).denominator_ne_zero
  intro hz
  exact hn (by simp [RrefResult.map, hz])

/-- Evaluate the output while retaining the original matrix and degree bounds. -/
theorem gosperSolve_output_map (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S) (r : Result R)
    (hrun : gosperSolve backend A B C = r)
    (hd : 0 ≤ degreeBound backend A B C) :
    let d := degreeBound backend A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let q := backend.rref (augmentedIdentity M)
    let y := (q.rightMatrix.map (algebraMap K S)).mulVec b
    0 ≤ d ∧ r.map f.toRingHom =
      { numerator := B.map (algebraMap K S) *
          ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (q.rawLeftSolution y j)
        denominator := Polynomial.C (algebraMap K S q.denominator) * C.map f.toRingHom
        residual := Polynomial.C (algebraMap K S q.denominator) * C.map f.toRingHom -
          (A.map (algebraMap K S) * taylor 1
              (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (q.rawLeftSolution y j)) -
            B.map (algebraMap K S) *
              ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (q.rawLeftSolution y j)) } := by
  have hvec {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) :
      f ∘ (M.map (algebraMap K R)).mulVec (toFn n C) =
        (M.map (algebraMap K S)).mulVec (toFn n (C.map f.toRingHom)) := by
    have hc : toFn n (C.map f.toRingHom) = f ∘ toFn n C := by ext i; simp [toFn]
    rw [hc]
    exact matrix_mulVec_map f M _
  rw [gosperSolve_eq backend hbackend] at hrun
  dsimp only at hrun ⊢
  simp only [not_lt.mpr hd, ↓reduceIte] at hrun
  cases hrun.symm
  refine ⟨hd, ?_⟩
  simp [Result.map, Polynomial.map_sum, Polynomial.map_map]
  let q := backend.rref (augmentedIdentity (coefficientSystem A B C
    (degreeBound backend A B C).toNat))
  have hr := (rawLeftSolution_map q f _).trans
    (congrArg q.rawLeftSolution (hvec q.rightMatrix))
  have hpoint := fun j => congrFun hr j
  dsimp only [q, Function.comp_apply] at hpoint
  simp only [hpoint]
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Rerunning commutes with a parameter map that preserves the input degree. -/
theorem gosperSolve_map (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S)
    (hdegree : (C.map f.toRingHom).natDegree = C.natDegree) :
    gosperSolve backend A B (C.map f.toRingHom) =
      (gosperSolve backend A B C).map f.toRingHom := by
  have hbound := degreeBound_rhs_eq backend A B (C.map f.toRingHom) C hdegree
  by_cases hd : degreeBound backend A B C < 0
  · rw [gosperSolve_of_degreeBound_neg backend A B C hd,
      gosperSolve_of_degreeBound_neg backend A B (C.map f.toRingHom) (by omega)]
    simp only [Result.map, Polynomial.map_zero]
  · have hd := not_lt.mp hd
    obtain ⟨_, he⟩ := gosperSolve_output_map backend hbackend A B C f
      (gosperSolve backend A B C) rfl hd
    rw [gosperSolve_eq backend hbackend, hbound]
    simp only [not_lt.mpr hd, ↓reduceIte]
    rw [he]
    delta coefficientSystem
    rw [hdegree]

/-- The degree bound computed over the coefficient domain controls solutions
in every faithful field target. -/
theorem domain_solution_degree_le [CharZero K] {T : Type*} [Semiring T]
    (backend : LinearBackend K) (hbackend : backend.Valid) (A B : K[X]) (C₀ : T[X]) (C x : E[X])
    (hKE : Function.Injective (algebraMap K E))
    (hdegree : C.natDegree ≤ C₀.natDegree) (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound backend A B C₀ :=
  solution_degree_le_extension_bounded backend hbackend A B C₀ C x hKE hdegree hA hB hx he

/-- The evaluated polynomial remainder vanishes exactly when the retained
matrix candidate solves the original coefficient system. -/
private theorem gosperSolve_residual_iff_system
    (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = r)
    (hd : 0 ≤ degreeBound backend A B C) :
    let d := degreeBound backend A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let q := (backend.rref (augmentedIdentity M)).map (algebraMap K E)
    r.residual.map f.toRingHom = 0 ↔
      (M.map (algebraMap K E)).mulVec (q.inverse.mulVec b) = b := by
  classical
  obtain ⟨_, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun hd
  let d := degreeBound backend A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q₀ := backend.rref (augmentedIdentity M)
  let q := q₀.map (algebraMap K E)
  have hq := backend.rref_valid_augmentedIdentity hbackend M (algebraMap K E) hKE
  have hδ : algebraMap K E q₀.denominator ≠ 0 := hq.denominator_ne_zero
  let x := ofFn (d.toNat + 1) (q.inverse.mulVec b)
  have hpoly : (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val
      (q₀.rawLeftSolution ((q₀.rightMatrix.map (algebraMap K E)).mulVec b) j)) =
      Polynomial.C (algebraMap K E q₀.denominator) * x := by
    dsimp only [x]
    rw [ofFn_eq_sum_monomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [q₀.rawLeftSolution_eq_denominator_mul_inverse (algebraMap K E) hδ b]
    simp [C_mul_monomial, q]
  have hres : r.residual.map f.toRingHom =
      Polynomial.C (algebraMap K E q₀.denominator) *
        (C.map f.toRingHom - forwardOperator (A.map (algebraMap K E))
          (B.map (algebraMap K E)) x) := by
    have hr := congrArg Result.residual he
    change r.residual.map f.toRingHom =
      Polynomial.C (algebraMap K E q₀.denominator) * C.map f.toRingHom -
        (A.map (algebraMap K E) * taylor 1
            (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val
              (q₀.rawLeftSolution ((q₀.rightMatrix.map (algebraMap K E)).mulVec b) j)) -
          B.map (algebraMap K E) *
            ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val
              (q₀.rawLeftSolution ((q₀.rightMatrix.map (algebraMap K E)).mulVec b) j)) at hr
    rw [hr, hpoly]
    simp only [forwardOperator_apply, taylor_mul, taylor_C]
    ring
  dsimp only
  rw [hres, mul_eq_zero, Polynomial.C_eq_zero, or_iff_right hδ, sub_eq_zero]
  exact eq_comm.trans (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
    d.toNat C.natDegree Polynomial.natDegree_map_le _).symm

/-- A vanishing evaluated remainder certifies a scaled normalized equation; the common
scale lies in `K` and remains nonzero in every faithful target field. -/
theorem gosperSolve_sound (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (_hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = r)
    (hzero : r.residual.map f.toRingHom = 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∃ x : E[X],
      r.numerator.map f.toRingHom = B.map (algebraMap K E) * x ∧
      r.denominator.map f.toRingHom = Polynomial.C (algebraMap K E δ) * C.map f.toRingHom ∧
      A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x =
        Polynomial.C (algebraMap K E δ) * C.map f.toRingHom := by
  obtain ⟨δ, hδ, x, hu, hv, he⟩ :=
    gosperSolve_reduction_data backend hbackend A B C r hrun
  have hu' := congrArg (Polynomial.map f.toRingHom) hu
  have hv' := congrArg (Polynomial.map f.toRingHom) hv
  have he' := congrArg (Polynomial.map f.toRingHom) he
  simp [Polynomial.map_map] at hu' hv' he'
  refine ⟨δ, hδ, x.map f.toRingHom, hu', hv', ?_⟩
  exact (sub_eq_zero.mp (hzero.symm.trans he').symm).symm.trans hv'

/-- Specialization may identify parameter values without changing the source reduction. -/
theorem gosperSolve_specialize_sound (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = r)
    (hzero : r.residual.map f.toRingHom = 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∃ x : E[X],
      r.numerator.map f.toRingHom = B.map (algebraMap K E) * x ∧
      r.denominator.map f.toRingHom = Polynomial.C (algebraMap K E δ) * C.map f.toRingHom ∧
      A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x =
        Polynomial.C (algebraMap K E δ) * C.map f.toRingHom :=
  gosperSolve_sound backend hbackend A B C f hKE r hrun hzero

/-- The vanishing remainder criterion is complete even when evaluation lowers the degree or
annihilates the entire right-hand side. -/
theorem gosperSolve_specialize_complete [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = r) (hA : A ≠ 0) (hB : B ≠ 0) :
    r.residual.map f.toRingHom = 0 ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom := by
  classical
  by_cases hd : degreeBound backend A B C < 0
  · rw [gosperSolve_of_degreeBound_neg backend A B C hd] at hrun
    cases hrun.symm
    constructor
    · intro hC
      exact ⟨0, by simpa using hC.symm⟩
    · rintro ⟨x, hx⟩
      by_cases hx0 : x = 0
      · simpa [hx0] using hx.symm
      · have hdn := domain_solution_degree_le backend hbackend A B C
          (C.map f.toRingHom) x hKE Polynomial.natDegree_map_le hA hB hx0 hx
        omega
  have hd := not_lt.mp hd
  let d := degreeBound backend A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q := (backend.rref (augmentedIdentity M)).map (algebraMap K E)
  have hq := backend.rref_valid_augmentedIdentity hbackend M (algebraMap K E) hKE
  have hi := gosperSolve_residual_iff_system backend hbackend A B C f hKE r hrun hd
  dsimp only at hi
  rw [hi]
  constructor
  · intro hs
    exact ⟨ofFn (d.toNat + 1) (q.inverse.mulVec b),
      (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
        d.toNat C.natDegree Polynomial.natDegree_map_le _).mp hs⟩
  · rintro ⟨x, hx⟩
    have hdn : x.natDegree ≤ d.toNat := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hd := domain_solution_degree_le backend hbackend A B C (C.map f.toRingHom) x hKE
          Polynomial.natDegree_map_le hA hB hx0 hx
        omega
    apply (q.inverse_solve_iff (M.map (algebraMap K E)) hq b).mpr
    refine ⟨toFn (d.toNat + 1) x,
      (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
        d.toNat C.natDegree Polynomial.natDegree_map_le _).mpr ?_⟩
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
    exact hx

/-- A nonzero specialized right-hand side has no polynomial solution when the
signed degree bound is negative. -/
theorem degreeBound_neg_not_solvable [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid) (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C.map f.toRingHom ≠ 0) (hd : degreeBound backend A B C < 0) :
    ¬ ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
      B.map (algebraMap K E) * x = C.map f.toRingHom := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by intro hz; apply hC; simpa [hz] using hx.symm
  have hdn := domain_solution_degree_le backend hbackend A B C (C.map f.toRingHom) x hKE
    Polynomial.natDegree_map_le hA hB hx0 hx
  omega

/-- The total solver's polynomial remainder vanishes precisely when the normalized equation
has a polynomial solution in the target field. -/
theorem gosperSolve_complete [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (hA : A ≠ 0) (hB : B ≠ 0) :
    (gosperSolve backend A B C).residual.map f.toRingHom = 0 ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom :=
  gosperSolve_specialize_complete backend hbackend A B C f hKE _ rfl hA hB

end Gosper.Algorithm
