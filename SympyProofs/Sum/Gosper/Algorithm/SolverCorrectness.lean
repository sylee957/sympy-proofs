module

public import SympyProofs.Sum.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Sum.Gosper.Algorithm.Degree
public import SympyProofs.Sum.Gosper.Algorithm.Horner
public import SympyProofs.Sum.Gosper.Backend.BareissInvariant
public import SympyProofs.Sum.Gosper.Backend.BareissLoop
public import SympyProofs.Sum.Gosper.Backend.Linear

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

variable [IsDomain K] [DecidableEq K] [Div K] [Div R] [Div S]
variable {W : Type} [CommRing W] [IsDomain W] [Algebra K W]

omit [Algebra K W] in
set_option backward.isDefEq.respectTransparency false in
private theorem gosperSolve_fused_eq (backend : TermBackend K W)
    (A B : K[X]) (C : R[X]) :
    gosperSolve backend A B C =
      let d := degreeBound backend A B C
      if d < 0 then
        { numerator := 0, denominator := C, residual := C }
      else
        let M := Vector.ofFn fun i => Vector.ofFn ((coefficientSystem A B C d.toNat) i)
        let b := Vector.ofFn fun i : Fin (max C.natDegree
          (max A.natDegree B.natDegree + d.toNat) + 1) => C.coeff i.val
        let steps := ((List.finRange (d.toNat + 1)).foldl bareissForwardStep (M, b, [], 1)).2.2.1
        let result := fusedBackSub steps (A.map (algebraMap K R)) (B.map (algebraMap K R))
        let V := Polynomial.C (algebraMap K R result.1) * C
        { numerator := result.2.2.1, denominator := V
          residual := V - (result.2.2.2 - result.2.2.1) } := by
  calc
    gosperSolve backend A B C = let d := degreeBound backend A B C
      if d < 0 then
        { numerator := 0, denominator := C, residual := C }
      else
        let M := Vector.ofFn fun i => Vector.ofFn ((coefficientSystem A B C d.toNat) i)
        let b := Vector.ofFn fun i : Fin (max C.natDegree
          (max A.natDegree B.natDegree + d.toNat) + 1) => C.coeff i.val
        let steps := (bareissForwardRun (List.finRange (d.toNat + 1)) M b [] 1).2.2.1
        let result := fusedBackSub steps (A.map (algebraMap K R)) (B.map (algebraMap K R))
        let V := Polynomial.C (algebraMap K R result.1) * C
        { numerator := result.2.2.1, denominator := V
          residual := V - (result.2.2.2 - result.2.2.1) } := by
      simp only [gosperSolve, bareissForwardRun, fusedBackSub, directDot, Vector.getElem_ofFn]
      rfl
    _ = _ := by simp only [bareissForwardRun_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Bareiss elimination returns the coefficient candidate and its common denominator. -/
theorem gosperSolve_eq (backend : TermBackend K W) (_hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) :
    gosperSolve backend A B C =
      let d := degreeBound backend A B C
      if d < 0 then
        { numerator := 0, denominator := C
          residual := C }
      else
        let M := coefficientSystem A B C d.toNat
        let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1) C
        let solution := bareissModel M b
        { numerator := B.map (algebraMap K R) *
            ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)
          denominator := Polynomial.C (algebraMap K R solution.1) * C
          residual := Polynomial.C (algebraMap K R solution.1) * C -
            (A.map (algebraMap K R) * taylor 1
                (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)) -
              B.map (algebraMap K R) *
                ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)) } := by
  rw [gosperSolve_fused_eq]
  dsimp only
  split_ifs
  · rfl
  · rw [fusedBackSub_eq _ _ _ (bareissForward_pivots_descending _ _ 1)]
    simp only [bareiss_forward_backward, List.foldl_nil,
      bareissModel]
    rfl

omit [Algebra K W] in
/-- A negative degree bound returns the complete right-hand side as a remainder. -/
theorem gosperSolve_of_degreeBound_neg (backend : TermBackend K W)
    (A B : K[X]) (C : R[X]) (hd : degreeBound backend A B C < 0) :
    gosperSolve backend A B C =
      { numerator := 0, denominator := C
        residual := C } := by
  simp [gosperSolve, hd]

/-- Every returned denominator is the supplied right-hand side multiplied by a nonzero
constant from the coefficient domain. -/
theorem gosperSolve_denominator (backend : TermBackend K W) (hbackend : backend.Valid)
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
  exact bareissModel_denominator_ne_zero _ _

/-- Every run supplies a polynomial reduction, whether or not the
polynomial remainder vanishes. -/
theorem gosperSolve_reduction_data (backend : TermBackend K W) (hbackend : backend.Valid)
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
  exact bareissModel_denominator_ne_zero _ _

/-- Evaluate the output while retaining the original matrix and degree bounds. -/
theorem gosperSolve_output_map [MulDivCancelClass K]
    [IsDomain R] [MulDivCancelClass R]
    [IsDomain S] [MulDivCancelClass S] [Module.IsTorsionFree K S]
    (backend : TermBackend K W) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] S) (r : Result R)
    (hrun : gosperSolve backend A B C = r)
    (hd : 0 ≤ degreeBound backend A B C) :
    let d := degreeBound backend A B C
    let M := coefficientSystem A B C d.toNat
    let b := toFn (max C.natDegree (max A.natDegree B.natDegree + d.toNat) + 1)
      (C.map f.toRingHom)
    let solution := bareissModel M b
    0 ≤ d ∧ r.map f.toRingHom =
      { numerator := B.map (algebraMap K S) *
          ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)
        denominator := Polynomial.C (algebraMap K S solution.1) * C.map f.toRingHom
        residual := Polynomial.C (algebraMap K S solution.1) * C.map f.toRingHom -
          (A.map (algebraMap K S) * taylor 1
              (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)) -
            B.map (algebraMap K S) *
              ∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)) } := by
  let : FaithfulSMul K R := (faithfulSMul_iff_algebraMap_injective K R).mpr (by
    intro a b h
    apply FaithfulSMul.algebraMap_injective K S
    simpa only [AlgHom.commutes] using congrArg f h)
  have hc (m : ℕ) : toFn m (C.map f.toRingHom) = f ∘ toFn m C := by
    ext i
    simp [toFn]
  rw [gosperSolve_eq backend hbackend] at hrun
  dsimp only at hrun ⊢
  simp only [not_lt.mpr hd, ↓reduceIte] at hrun
  cases hrun.symm
  refine ⟨hd, ?_⟩
  simp only [hc]
  rw [bareissModel_map f _ _ (bareiss_exactDivisions _ _ _)]
  simp [Result.map, Polynomial.map_sum, Polynomial.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Rerunning commutes with a parameter map that preserves the input degree. -/
theorem gosperSolve_map [MulDivCancelClass K]
    [IsDomain R] [MulDivCancelClass R]
    [IsDomain S] [MulDivCancelClass S] [Module.IsTorsionFree K S]
    (backend : TermBackend K W) (hbackend : backend.Valid)
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

omit [Div K] in
/-- The degree bound computed over the coefficient domain controls solutions
in every faithful field target. -/
theorem domain_solution_degree_le [CharZero K] {T : Type*} [Semiring T]
    (backend : TermBackend K W) (hbackend : backend.Valid) (A B : K[X]) (C₀ : T[X]) (C x : E[X])
    (hKE : Function.Injective (algebraMap K E))
    (hdegree : C.natDegree ≤ C₀.natDegree) (hA : A ≠ 0) (hB : B ≠ 0) (hx : x ≠ 0)
    (he : A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x = C) :
    (x.natDegree : ℤ) ≤ degreeBound backend A B C₀ :=
  solution_degree_le_extension_bounded backend hbackend A B C₀ C x hKE hdegree hA hB hx he

/-- A vanishing evaluated remainder certifies a scaled normalized equation; the common
scale lies in `K` and remains nonzero in every faithful target field. -/
theorem gosperSolve_sound (backend : TermBackend K W) (hbackend : backend.Valid)
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
theorem gosperSolve_specialize_sound (backend : TermBackend K W) (hbackend : backend.Valid)
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
theorem gosperSolve_specialize_complete [CharZero K] [MulDivCancelClass K]
    [IsDomain R] [MulDivCancelClass R]
    (backend : TermBackend K W) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (r : Result R)
    (hrun : gosperSolve backend A B C = r) (hA : A ≠ 0) (hB : B ≠ 0) :
    r.residual.map f.toRingHom = 0 ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom := by
  classical
  let : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).mpr hKE
  constructor
  · intro hzero
    obtain ⟨δ, hδ, x, _, _, hx⟩ :=
      gosperSolve_sound backend hbackend A B C f hKE r hrun hzero
    have hδ' : algebraMap K E δ ≠ 0 := by
      intro hz
      exact hδ (hKE (hz.trans (map_zero _).symm))
    refine ⟨Polynomial.C ((algebraMap K E δ)⁻¹) * x, ?_⟩
    calc
      _ = Polynomial.C ((algebraMap K E δ)⁻¹) *
          (A.map (algebraMap K E) * taylor 1 x - B.map (algebraMap K E) * x) := by
        simp only [taylor_mul, taylor_C]
        ring
      _ = Polynomial.C ((algebraMap K E δ)⁻¹) *
          (Polynomial.C (algebraMap K E δ) * C.map f.toRingHom) := by rw [hx]
      _ = C.map f.toRingHom := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hδ', Polynomial.C_1, one_mul]
  · rintro ⟨x, hx⟩
    by_cases hd : degreeBound backend A B C < 0
    · rw [gosperSolve_of_degreeBound_neg backend A B C hd] at hrun
      cases hrun.symm
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
    let solution := bareissModel M b
    have hdn : x.natDegree ≤ d.toNat := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hbound := domain_solution_degree_le backend hbackend A B C (C.map f.toRingHom)
          x hKE Polynomial.natDegree_map_le hA hB hx0 hx
        omega
    have hsystem : ∃ v, (M.map (algebraMap K E)).mulVec v = b := by
      refine ⟨toFn (d.toNat + 1) x,
        (coefficientSystem_correct_extension_bounded A B (C.map f.toRingHom)
          d.toNat C.natDegree Polynomial.natDegree_map_le _).mpr ?_⟩
      rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
      exact hx
    have hscaled := bareissModel_complete M b (bareiss_exactDivisions _ _ _) hsystem
    have hpoly : forwardOperator (A.map (algebraMap K E)) (B.map (algebraMap K E))
        (ofFn (d.toNat + 1) solution.2) =
        Polynomial.C (algebraMap K E solution.1) * C.map f.toRingHom := by
      apply (coefficientSystem_correct_extension_bounded A B
        (Polynomial.C (algebraMap K E solution.1) * C.map f.toRingHom)
        d.toNat C.natDegree
        ((natDegree_C_mul_le _ _).trans Polynomial.natDegree_map_le) solution.2).mp
      change (M.map (algebraMap K E)).mulVec solution.2 = _
      rw [hscaled]
      ext i
      simp [solution, b, toFn, Pi.smul_apply, smul_eq_mul]
    obtain ⟨_, he⟩ := gosperSolve_output_map backend hbackend A B C f r hrun hd
    have hres := congrArg Result.residual he
    change r.residual.map f.toRingHom =
      Polynomial.C (algebraMap K E solution.1) * C.map f.toRingHom -
        forwardOperator (A.map (algebraMap K E)) (B.map (algebraMap K E))
          (∑ j : Fin (d.toNat + 1), Polynomial.monomial j.val (solution.2 j)) at hres
    rw [← ofFn_eq_sum_monomial, hpoly, sub_self] at hres
    exact hres

omit [Div K] [Div R] in
/-- A nonzero specialized right-hand side has no polynomial solution when the
signed degree bound is negative. -/
theorem degreeBound_neg_not_solvable [CharZero K]
    (backend : TermBackend K W) (hbackend : backend.Valid) (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
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
theorem gosperSolve_complete [CharZero K] [MulDivCancelClass K]
    [IsDomain R] [MulDivCancelClass R]
    (backend : TermBackend K W) (hbackend : backend.Valid)
    (A B : K[X]) (C : R[X]) (f : R →ₐ[K] E)
    (hKE : Function.Injective (algebraMap K E)) (hA : A ≠ 0) (hB : B ≠ 0) :
    (gosperSolve backend A B C).residual.map f.toRingHom = 0 ↔
      ∃ x : E[X], A.map (algebraMap K E) * taylor 1 x -
        B.map (algebraMap K E) * x = C.map f.toRingHom :=
  gosperSolve_specialize_complete backend hbackend A B C f hKE _ rfl hA hB

end Gosper.Algorithm
