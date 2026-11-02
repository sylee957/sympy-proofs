module

public import SympyProofs.Sum.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Sum.Gosper.Algorithm.Degree
public import SympyProofs.Sum.Gosper.Backend.LinearAlgebra

/-! Fraction-free normalized solving and evaluation of its retained conditions. -/

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
  · exact (Array.map_inj_right (fun _ _ he => hf he)).mp (congrArg Result.residual h)

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
      if d < 0 then none else
        let M := coefficientSystem A B C d.toNat
        let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1) C
        let r := backend.rref (augmentedIdentity M)
        let y := (r.rightMatrix.map (algebraMap K R)).mulVec b
        some { numerator := B.map (algebraMap K R) *
                 ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (r.rawLeftSolution y j)
               denominator := Polynomial.C (algebraMap K R r.denominator) * C
               residual := r.residualEntries y } := by
  let d := degreeBound backend A B C
  have hM := backend.fill_identity_augmented_eq hbackend (coefficientSystem A B C d.toNat)
  simp only [Id.run, bind, pure, coefficientSystem, forwardOperator_apply] at hM
  dsimp only [d] at hM
  have htransform {m n : ℕ} (r : RrefResult K m (n + m)) (values : Fin m → R) :=
    r.transform_rhs_ring_vector_eq values
  simp only [Id.run, bind, pure] at htransform
  have hextract {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) :=
    (backend.rref M).extract_raw_vector_residual_eq (hbackend.rref_valid M).ordered values
  have hcoefficients {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) := congrArg Prod.fst (hextract M values)
  have hresidual {m n : ℕ} (M : Matrix (Fin m) (Fin (n + m)) K)
      (values : Fin m → R) := congrArg Prod.snd (hextract M values)
  simp only [Id.run, bind, pure] at hcoefficients hresidual
  have hget {m : ℕ} (values : Fin m → R) (i : Fin m) :
      (Vector.ofFn values)[i.val] = values i := by simp
  simp only [gosperSolve, Id.run, bind, pure, toFn]
  simp only [htransform, hcoefficients, hresidual, hget]
  rw [hM]
  rfl

/-- A negative signed degree bound is the solver's only failure branch. -/
theorem gosperSolve_none_iff_degreeBound_neg (backend : LinearBackend K)
    (A B : K[X]) (C : R[X]) :
    gosperSolve backend A B C = none ↔
      degreeBound backend A B C < 0 := by
  simp only [gosperSolve, Id.run, bind, pure]
  split_ifs <;> simp_all

/-- Every returned denominator is the supplied right-hand side multiplied by a nonzero
constant from the coefficient domain. -/
theorem gosperSolve_denominator (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) :
    ∃ δ : K, δ ≠ 0 ∧ r.denominator = Polynomial.C (algebraMap K R δ) * C := by
  rw [gosperSolve_eq backend hbackend A B C] at hrun
  dsimp only at hrun
  split_ifs at hrun
  cases Option.some.inj hrun
  refine ⟨_, ?_, rfl⟩
  have hn := (hbackend.rref_valid (augmentedIdentity
    (coefficientSystem A B C (degreeBound backend A B C).toNat))).denominator_ne_zero
  intro hz
  exact hn (by simp [RrefResult.map, hz])

/-- Evaluate the output while retaining the original matrix and degree bounds. -/
theorem gosperSolve_output_map (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) :
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
        residual := q.residualEntries y } := by
  have hvec {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) :
      f ∘ (M.map (algebraMap K R)).mulVec (toFn n C) =
        (M.map (algebraMap K S)).mulVec (toFn n (C.map f.toRingHom)) := by
    have hc : toFn n (C.map f.toRingHom) = f ∘ toFn n C := by ext i; simp [toFn]
    rw [hc]
    exact matrix_mulVec_map f M _
  rw [gosperSolve_eq backend hbackend] at hrun
  dsimp only at hrun ⊢
  split_ifs at hrun with hd
  cases Option.some.inj hrun
  refine ⟨not_lt.mp hd, ?_⟩
  simp [Result.map, Polynomial.map_sum, Polynomial.map_map,
    RrefResult.residualEntries_map, Function.comp_def]
  let q := backend.rref (augmentedIdentity (coefficientSystem A B C
    (degreeBound backend A B C).toNat))
  constructor
  · apply congrArg (fun p : S[X] => B.map (algebraMap K S) * p)
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (Polynomial.monomial j.val)
    have hr := (rawLeftSolution_map q f _).trans
      (congrArg q.rawLeftSolution (hvec q.rightMatrix))
    exact congrFun hr j
  · exact congrArg q.residualEntries (hvec q.rightMatrix)

set_option backward.isDefEq.respectTransparency false in
/-- Rerunning commutes with a parameter map that preserves the input degree. -/
theorem gosperSolve_map (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S)
    (hdegree : (C.map f.toRingHom).natDegree = C.natDegree) :
    gosperSolve backend A B (C.map f.toRingHom) =
      (gosperSolve backend A B C).map (Result.map f.toRingHom) := by
  cases hrun : gosperSolve backend A B C with
  | none =>
      simp only [Option.map_none]
      rw [gosperSolve_none_iff_degreeBound_neg]
      rw [degreeBound_rhs_eq backend _ _ (C.map f.toRingHom) C hdegree]
      exact (gosperSolve_none_iff_degreeBound_neg backend A B C).mp hrun
  | some r =>
      simp only [Option.map_some]
      obtain ⟨hd, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun
      rw [gosperSolve_eq backend hbackend]
      rw [degreeBound_rhs_eq backend _ _ (C.map f.toRingHom) C hdegree]
      simp only [not_lt.mpr hd, ↓reduceIte]
      congr 1
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

/-- The retained conditions are precisely the consistency equations of the original matrix. -/
theorem gosperSolve_residual_iff_system (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) :
    let d := degreeBound backend A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let q := (backend.rref (augmentedIdentity M)).map (algebraMap K E)
    (∀ value ∈ r.residual, f value = 0) ↔
      (M.map (algebraMap K E)).mulVec (q.inverse.mulVec b) = b := by
  obtain ⟨_, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun
  dsimp only
  let d := degreeBound backend A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q := (backend.rref (augmentedIdentity M)).map (algebraMap K E)
  have hq := backend.rref_valid_augmentedIdentity hbackend M (algebraMap K E) hKE
  have hz : (∀ value ∈ r.residual, f value = 0) ↔
      (∀ value ∈ q.residualEntries (q.rightMatrix.mulVec b), value = 0) := by
    have hre := congrArg Result.residual he
    change r.residual.map f.toRingHom = q.residualEntries (q.rightMatrix.mulVec b) at hre
    rw [← hre]
    simp [Array.mem_map]
  exact hz.trans ((q.residualEntries_zero_iff hq b).trans
    (q.leftResidual_eq_zero_iff (M.map (algebraMap K E)) hq b))

/-- Vanishing evaluated conditions certify a scaled normalized equation; the common
scale lies in `K` and remains nonzero in every faithful target field. -/
theorem gosperSolve_sound (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = some r)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∃ x : E[X],
      r.numerator.map f.toRingHom = B.map (algebraMap K E) * x ∧
      r.denominator.map f.toRingHom = Polynomial.C (algebraMap K E δ) * C.map f.toRingHom ∧
      A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x =
        Polynomial.C (algebraMap K E δ) * C.map f.toRingHom := by
  classical
  obtain ⟨_, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun
  let d := degreeBound backend A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q₀ := backend.rref (augmentedIdentity M)
  let q := q₀.map (algebraMap K E)
  have hq := backend.rref_valid_augmentedIdentity hbackend M (algebraMap K E) hKE
  have hδ : algebraMap K E q₀.denominator ≠ 0 := hq.denominator_ne_zero
  have hδ₀ : q₀.denominator ≠ 0 := by intro hz; exact hδ (by simp [hz])
  have hs := (gosperSolve_residual_iff_system backend hbackend A B C f hKE r hrun).mp hzero
  have hx₀ : A.map (algebraMap K E) * taylor 1 (ofFn (d.toNat + 1) (q.inverse.mulVec b)) -
      B.map (algebraMap K E) * ofFn (d.toNat + 1) (q.inverse.mulVec b) = C.map f.toRingHom :=
    (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
      d.toNat C.natDegree Polynomial.natDegree_map_le _).mp hs
  let x := Polynomial.C (algebraMap K E q₀.denominator) *
    ofFn (d.toNat + 1) (q.inverse.mulVec b)
  have hpoly : (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val
      (q₀.rawLeftSolution ((q₀.rightMatrix.map (algebraMap K E)).mulVec b) j)) = x := by
    dsimp only [x]
    rw [ofFn_eq_sum_monomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [q₀.rawLeftSolution_eq_denominator_mul_inverse (algebraMap K E) hδ b]
    simp [C_mul_monomial, q]
  refine ⟨q₀.denominator, hδ₀, x, ?_, ?_, ?_⟩
  · have hu := congrArg Result.numerator he
    change r.numerator.map f.toRingHom = B.map (algebraMap K E) * _ at hu
    rw [hpoly] at hu
    exact hu
  · exact congrArg Result.denominator he
  · dsimp only [x]
    simp only [taylor_mul, taylor_C]
    linear_combination Polynomial.C (algebraMap K E q₀.denominator) * hx₀

/-- Specialization may identify parameter values without changing the source reduction. -/
theorem gosperSolve_specialize_sound (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = some r)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∃ x : E[X],
      r.numerator.map f.toRingHom = B.map (algebraMap K E) * x ∧
      r.denominator.map f.toRingHom = Polynomial.C (algebraMap K E δ) * C.map f.toRingHom ∧
      A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x =
        Polynomial.C (algebraMap K E δ) * C.map f.toRingHom :=
  gosperSolve_sound backend hbackend A B C f hKE r hrun hzero

/-- The residual criterion is complete even when evaluation lowers the degree or
annihilates the entire right-hand side. -/
theorem gosperSolve_specialize_complete [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = some r) (hA : A ≠ 0) (hB : B ≠ 0) :
    (∀ value ∈ r.residual, f value = 0) ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom := by
  classical
  let d := degreeBound backend A B C
  let M := coefficientSystem A B C d.toNat
  let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
    (C.map f.toRingHom)
  let q := (backend.rref (augmentedIdentity M)).map (algebraMap K E)
  have hq := backend.rref_valid_augmentedIdentity hbackend M (algebraMap K E) hKE
  have hi := gosperSolve_residual_iff_system backend hbackend A B C f hKE r hrun
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

/-- A nonzero specialized right-hand side with a solution cannot take the negative-bound branch. -/
theorem gosperSolve_none_not_solvable [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid) (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C.map f.toRingHom ≠ 0) (hrun : gosperSolve backend A B C = none) :
    ¬ ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
      B.map (algebraMap K E) * x = C.map f.toRingHom := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by intro hz; apply hC; simpa [hz] using hx.symm
  have hd := domain_solution_degree_le backend hbackend A B C (C.map f.toRingHom) x hKE
    Polynomial.natDegree_map_le hA hB hx0 hx
  have hn := (gosperSolve_none_iff_degreeBound_neg backend A B C).mp hrun
  omega

/-- For a nonzero evaluated right-hand side, existence of an output with vanishing
conditions is equivalent to polynomial solvability in the target field. -/
theorem gosperSolve_complete [CharZero K]
    (backend : LinearBackend K) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C.map f.toRingHom ≠ 0) :
    (∃ r, gosperSolve backend A B C = some r ∧ ∀ value ∈ r.residual, f value = 0) ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom := by
  cases hrun : gosperSolve backend A B C with
  | none =>
      simp only [reduceCtorEq, false_and, exists_false, false_iff]
      exact gosperSolve_none_not_solvable backend hbackend A B C f hKE hA hB hC hrun
  | some r =>
      simp only [Option.some.injEq, exists_eq_left']
      exact gosperSolve_specialize_complete backend hbackend A B C f hKE r hrun hA hB

end Gosper.Algorithm
