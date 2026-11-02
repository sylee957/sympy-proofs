module

public import SympyProofs.Sum.Gosper.Algorithm.Correctness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness

/-! Completeness of Gosper reconstruction, conditional on successful coefficient descent. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K]

theorem normalForm_backwardRatio (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
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

theorem normalForm_hypergeometric_iff_polynomial [CharZero K]
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (s : K[X] × K[X] × K[X]) (hs : normalFormValid P Q s) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) ↔
      ∃ x : K[X], s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2 := by
  have hρ : Gosper.rationalShift (-1) (toRatFunc P Q) ≠ 0 := by
    simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial]
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  have hA : taylor (-1 : K) s.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.1
  have hB : taylor (-1 : K) s.2.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.2.1
  have hcop : Gosper.ShiftCoprime (taylor (-1) s.1) (taylor (-1) s.2.1) := by
    intro j
    simpa [taylor_taylor, add_comm] using (hs.2.1 j).map (taylorAlgHom (-1 : K)).toRingHom
  rw [Gosper.hypergeometric_iff_rational _ hρ, normalForm_backwardRatio P Q hQ s hs,
    Gosper.summable_iff_rational_solution _ _ _ hs.1.2.2 hA hB,
    Gosper.rational_solution_iff_polynomial _ _ _ hcop]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨taylor (-1) f, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hf
  · rintro ⟨x, hx⟩
    refine ⟨taylor 1 x, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hx

theorem normalForm_verify_solution [DecidableEq K]
    (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hs : normalFormValid P Q s) (x : K[X])
    (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true :=
  normalForm_verify_solution_of_ratio P Q hQ s hs.1.2.2 hs.2.2 x hx

variable [CharZero K] [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
  [DecidablePred (IsInteger ℤ : L → Prop)] [Algebra K L]
variable (backend : TermBackend K L)

/-- A run without a descent error is complete over `L`, while its matrix is solved over `K`. -/
theorem gosperTerm_complete (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (result : Option (Result L))
    (hrun : gosperTerm backend P Q = .ok result) :
    (∃ c, result = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  obtain ⟨A, B, hA, hB, hsolve⟩ :=
    (gosperTerm_eq_ok_iff backend P Q result).mp hrun
  have hmapA := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  have hmapB' : (taylor (-1) B).map (algebraMap K L) =
      taylor (-1) (gosperNormal backend.normalization P Q).2.1 := by simp [hmapB]
  obtain ⟨s, hs, hvalid⟩ :=
    gosperNormal_exists backend.normalization hbackend.normalization P Q hP hQ
  subst s
  have hA0 : A ≠ 0 := by
    intro hz
    apply hvalid.1.1
    rw [← hmapA, hz, Polynomial.map_zero]
  have hB0 : B ≠ 0 := by
    intro hz
    apply hvalid.1.2.1
    rw [← hmapB, hz, Polynomial.map_zero]
  have hBshift : taylor (-1) B ≠ 0 := (taylor_eq_zero _ _).not.mpr hB0
  rw [← hsolve, gosperSolve_complete backend.solver hbackend.solver A (taylor (-1) B) _
    hA0 hBshift hvalid.1.2.2]
  rw [hmapA, hmapB']
  exact (normalForm_hypergeometric_iff_polynomial P Q hP hQ _ hvalid).symm

/-- `ok none` means nonsummability, rather than a failed coefficient descent. -/
theorem gosperTerm_none_not_summable (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : gosperTerm backend P Q = .ok none) :
    ¬Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  simpa using (gosperTerm_complete backend hbackend P Q hP hQ none h).not

/-- For a returned result, the retained residual vanishes exactly when the input is summable. -/
theorem gosperTerm_result_complete (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c)) :
    (∀ value ∈ c.residual, value = 0) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  simpa using gosperTerm_complete backend hbackend P Q hP hQ (some c) h

/-- Without a descent error, `none` proves nonsummability and a candidate's residual
exactly characterizes summability. A vanishing residual verifies that candidate. -/
theorem gosperTerm_spec (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Option (Result L))
    (hrun : gosperTerm backend P Q = .ok result) :
    match result with
    | none => ¬Gosper.HasHypergeometricAntidifference
        (Gosper.rationalShift (-1) (toRatFunc P Q))
    | some c =>
        ((∀ value ∈ c.residual, value = 0) ↔ Gosper.HasHypergeometricAntidifference
          (Gosper.rationalShift (-1) (toRatFunc P Q))) ∧
        ((∀ value ∈ c.residual, value = 0) → verify P Q c.numerator c.denominator = true) := by
  cases result with
  | none =>
      exact gosperTerm_none_not_summable backend hbackend P Q hP hQ hrun
  | some c =>
      exact ⟨gosperTerm_result_complete backend hbackend P Q hP hQ c hrun,
        gosperTerm_verified backend hbackend P Q hP hQ c hrun⟩

/-- Valid backends agree on summability when neither run returns a descent error. -/
theorem gosperTerm_success_iff (hbackend : backend.Valid)
    (other : TermBackend K L) (hother : other.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (result otherResult : Option (Result L))
    (hrun : gosperTerm backend P Q = .ok result)
    (hotherRun : gosperTerm other P Q = .ok otherResult) :
    (∃ c, result = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      ∃ c, otherResult = some c ∧ (∀ value ∈ c.residual, value = 0) := by
  rw [gosperTerm_complete backend hbackend P Q hP hQ result hrun,
    gosperTerm_complete other hother P Q hP hQ otherResult hotherRun]

/-- Reference polynomial operations and valid RREFs instantiate the completeness theorem. -/
theorem reference_gosperTerm_complete (descendCoeff : L → Option K)
    (rrefL : RrefOperation L) (rrefK : RrefOperation K)
    (hrrefL : ∀ {m n} (A : Matrix (Fin m) (Fin n) L), (rrefL A).Valid A)
    (hrrefK : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rrefK A).Valid A)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Option (Result L))
    (hrun : gosperTerm
      { normalization := referenceBackend rrefL
        solver := referenceBackend rrefK
        descend := descendCoeff } P Q = .ok result) :
    (∃ c, result = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) :=
  gosperTerm_complete
    { normalization := referenceBackend rrefL
      solver := referenceBackend rrefK
      descend := descendCoeff }
    { normalization := referenceBackend_valid rrefL hrrefL
      solver := referenceBackend_valid rrefK hrrefK
      descend := hdesc }
    P Q hP hQ result hrun

end Gosper.Algorithm
