module

public import SympyProofs.Sum.Gosper.Algorithm.Correctness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.RationalExtension

/-! Completeness of Gosper reconstruction, conditional on successful coefficient descent. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {K : Type}

theorem normalForm_backwardRatio [Field K] (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hs : normalFormValid P Q s) :
    Gosper.rationalShift (-1) (toRatFunc P Q) =
      Gosper.normalRatio s.2.2 (taylor (-1) s.1) (taylor (-1) s.2.1) := by
  let ι := algebraMap K[X] (RatFunc K)
  have hq : ι (taylor (-1) Q) ≠ 0 := by simpa [ι] using hQ
  have hd : ι (taylor (-1) s.2.2 * taylor (-1) s.2.1) ≠ 0 := by
    simpa [ι] using mul_ne_zero hs.1.2.2 hs.1.2.1
  simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial, Gosper.normalRatio]
  apply (div_eq_div_iff hq hd).mpr
  have he := congrArg (taylor (-1)) hs.2.2
  simp only [taylor_mul, taylor_taylor, neg_add_cancel, taylor_zero] at he
  simpa only [ι, ← map_mul, mul_assoc, mul_comm, mul_left_comm] using congrArg ι he

theorem normalForm_hypergeometric_iff_polynomial [Field K] [CharZero K]
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (s : K[X] × K[X] × K[X]) (hs : normalFormValid P Q s) :
    Gosper.HasHypergeometricAntidifference (toRatFunc P Q) ↔
      ∃ x : K[X], s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2 := by
  have hρ : toRatFunc P Q ≠ 0 := by
    unfold toRatFunc
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  have hA : taylor (-1 : K) s.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.1
  have hB : taylor (-1 : K) s.2.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.2.1
  have hcop : Gosper.ShiftCoprime (taylor (-1) s.1) (taylor (-1) s.2.1) := by
    intro j
    simpa [taylor_taylor, add_comm] using (hs.2.1 j).map (taylorAlgHom (-1 : K)).toRingHom
  rw [Gosper.hypergeometric_iff_forward _ hρ, forward_iff_backward,
    normalForm_backwardRatio P Q hQ s hs,
    Gosper.summable_iff_rational_solution _ _ _ hs.1.2.2 hA hB,
    Gosper.rational_solution_iff_polynomial _ _ _ hcop]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨taylor (-1) f, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hf
  · rintro ⟨x, hx⟩
    refine ⟨taylor 1 x, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hx

variable [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
variable {L : Type} [CommRing L] [IsDomain L] [CharZero L] [Algebra K L]
variable (backend : TermBackend K L)

/-- A run without a descent error is complete for rational functions over `L`. -/
theorem gosperTerm_complete (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (result : Result L)
    (hrun : gosperTerm backend P Q = .ok result) :
    result.residual = 0 ↔
      Gosper.HasHypergeometricAntidifference (toRatFunc P Q) := by
  have htransport : Gosper.HasHypergeometricAntidifference (toRatFunc P Q) ↔
      Gosper.HasHypergeometricAntidifference
        (toRatFunc (P.map (algebraMap L (FractionRing L)))
          (Q.map (algebraMap L (FractionRing L)))) := by
    simpa only [toRatFunc, map_div₀, Gosper.fractionRingRatFuncEquiv_polynomial] using
      Gosper.hasHypergeometricAntidifference_equiv (Gosper.fractionRingRatFuncEquiv L)
        (fun f => by simp)
        (toRatFunc P Q)
  rw [htransport]
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_normalForm backend hbackend P Q hP hQ result hrun
  have hi := IsFractionRing.injective L (FractionRing L)
  have hA : A ≠ 0 := by
    intro h
    simpa [h] using hvalid.1.1
  have hB : B ≠ 0 := by
    intro h
    simpa [h] using hvalid.1.2.1
  have hBshift : taylor (-1) B ≠ 0 := (taylor_eq_zero _ _).not.mpr hB
  have hKi : Function.Injective (algebraMap K (FractionRing L)) := by
    rw [IsScalarTower.algebraMap_eq K L (FractionRing L)]
    exact hi.comp hbackend.algebraMap_injective
  have hcomplete := gosperSolve_complete backend hbackend
    A (taylor (-1) B) C (IsScalarTower.toAlgHom K L (FractionRing L))
    hKi hA hBshift
  have hmap : Function.Injective
      (IsScalarTower.toAlgHom K L (FractionRing L)).toRingHom := hi
  simp only [Polynomial.map_eq_zero_iff hmap] at hcomplete
  rw [← hsolve, hcomplete]
  have hPf : P.map (algebraMap L (FractionRing L)) ≠ 0 :=
    fun h => hP ((Polynomial.map_injective _ hi) (by simpa using h))
  have hQf : Q.map (algebraMap L (FractionRing L)) ≠ 0 :=
    fun h => hQ ((Polynomial.map_injective _ hi) (by simpa using h))
  simpa using (normalForm_hypergeometric_iff_polynomial _ _ hPf hQf _ hvalid).symm

/-- For a returned result, the residual vanishes exactly when the input is summable. -/
theorem gosperTerm_result_complete (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c) :
    c.residual = 0 ↔
      Gosper.HasHypergeometricAntidifference (toRatFunc P Q) := by
  simpa using gosperTerm_complete backend hbackend P Q hP hQ c h

/-- The actual residual is zero exactly when the input is hypergeometrically summable. -/
theorem gosperTerm_residual_complete (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r) :
    r.residual = 0 ↔ Gosper.HasHypergeometricAntidifference (toRatFunc P Q) := by
  exact gosperTerm_result_complete backend hbackend P Q hP hQ r hrun

/-- Without a descent error, the residual exactly characterizes summability.
A vanishing residual verifies the returned candidate. -/
theorem gosperTerm_spec [DecidableEq L] (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Result L)
    (hrun : gosperTerm backend P Q = .ok result) :
    (result.residual = 0 ↔
      Gosper.HasHypergeometricAntidifference (toRatFunc P Q)) ∧
    (result.residual = 0 →
      verify P Q result.numerator result.denominator = true) := by
  exact ⟨gosperTerm_complete backend hbackend P Q hP hQ result hrun,
    gosperTerm_verified backend hbackend P Q hP hQ result hrun⟩

/-- Valid backends agree on summability when neither run returns a descent error. -/
theorem gosperTerm_success_iff (hbackend : backend.Valid)
    (other : TermBackend K L) (hother : other.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (result otherResult : Result L)
    (hrun : gosperTerm backend P Q = .ok result)
    (hotherRun : gosperTerm other P Q = .ok otherResult) :
    result.residual = 0 ↔ otherResult.residual = 0 := by
  rw [gosperTerm_complete backend hbackend P Q hP hQ result hrun,
    gosperTerm_complete other hother P Q hP hQ otherResult hotherRun]

/-- Replacing integer-ratio recognition with another valid implementation preserves completeness. -/
theorem reference_gosperTerm_complete (hbackend : backend.Valid)
    (integerRatio : K → K → Option ℤ)
    (hintegerRatio : ∀ a b, b ≠ 0 → ∀ z : ℤ,
      integerRatio a b = some z ↔ a = (z : K) * b)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Result L)
    (hrun : gosperTerm
      { backend with integerRatio := integerRatio }
      P Q = .ok result) :
    result.residual = 0 ↔
      Gosper.HasHypergeometricAntidifference (toRatFunc P Q) := by
  apply gosperTerm_complete _ ?_ P Q hP hQ result hrun
  exact { hbackend with integerRatio_eq_some := hintegerRatio }

end Gosper.Algorithm
