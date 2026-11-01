module

public import SympyProofs.Sum.Gosper.Algorithm.Correctness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness

/-! Completeness of normalization, bounded solving, and Gosper reconstruction. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [CharZero K]
variable (backend : Backend K)

omit [CharZero K] in
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

theorem normalForm_hypergeometric_iff_polynomial (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
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

variable [DecidableEq K]

omit [CharZero K] in
theorem normalForm_verify_solution (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hs : normalFormValid P Q s) (x : K[X])
    (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true :=
  normalForm_verify_solution_of_ratio P Q hQ s hs.1.2.2 hs.2.2 x hx

variable [DecidablePred (IsInteger ℤ : K → Prop)]

/-- A normalized polynomial solution lies within the degree bound, so applying
the generalized inverse solves its coefficient system and yields a valid certificate. -/
theorem gosperTerm_of_solution_self (hbackend : backend.Valid) (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hn : gosperNormal backend P Q = s) (hs : normalFormValid P Q s) (x : K[X])
    (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    ∃ c, gosperTerm backend backend some P Q = .ok (some c) ∧ (∀ value ∈ c.residual, value = 0) ∧
      verify P Q c.numerator c.denominator = true := by
  subst s
  let s := gosperNormal backend P Q
  let B := taylor (-1) s.2.1
  let d := degreeBound s.1 B s.2.2
  let M := coefficientSystem s.1 B s.2.2 d.toNat
  let b := toFn (max s.2.2.natDegree (max s.1.natDegree B.natDegree + d.toNat) + 1) s.2.2
  let coeffs := (inverseRref backend.rref M).mulVec b
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx; exact hs.1.2.2 hx.symm
  have hB : B ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.2.1
  have hdeg := solution_degree_le s.1 B s.2.2 x hs.1.1 hB hx0 hx
  have hd : 0 ≤ d := le_trans (by omega) hdeg
  have hdn : x.natDegree ≤ d.toNat := by omega
  have hm : ∃ c, M.mulVec c = b := by
    refine ⟨toFn (d.toNat + 1) x, (coefficientSystem_correct _ _ _ _ _).mpr ?_⟩
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
    exact hx
  have hcoeffs : M.mulVec coeffs = b :=
    (inverseRref_solve_iff backend.rref hbackend.rref_valid M b).mpr hm
  let y := ofFn (d.toNat + 1) coeffs
  have hy : s.1 * taylor 1 y - B * y = s.2.2 :=
    (coefficientSystem_correct _ _ _ _ _).mp hcoeffs
  let r := backend.rref (augmentedIdentity M)
  have hres : r.leftResidual (r.rightMatrix.mulVec b) = 0 :=
    (r.leftResidual_eq_zero_iff M (hbackend.rref_valid _) b).mpr hcoeffs
  refine ⟨{ numerator := B * y
            denominator := s.2.2
            residual := r.residualEntries (r.rightMatrix.mulVec b) }, ?_, ?_, ?_⟩
  · rw [gosperTerm_eq_self backend hbackend]
    simp only [Except.ok.injEq]
    change (if d < 0 then none else some
      ({ numerator := B * y
         denominator := s.2.2
         residual := r.residualEntries (r.rightMatrix.mulVec b) } : Result K)) = _
    simp [not_lt.mpr hd]
  · exact (r.residualEntries_zero_iff (hbackend.rref_valid _) b).mpr hres
  · exact normalForm_verify_solution P Q hQ s hs y hy

/-- A returned candidate with vanishing residual exists exactly when the paper's
hypergeometric antidifference exists. The shift converts the input's forward ratio
a(n+1)/a(n) to the backward ratio a(n)/a(n-1) used by the specification. -/
theorem gosperTerm_complete_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm backend backend some P Q = .ok (some c) ∧ (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  constructor
  · rintro ⟨c, hc, hzero⟩
    exact gosperTerm_hypergeometric_self backend hbackend P Q hP hQ c hc hzero
  · intro hh
    obtain ⟨s, hn, hs⟩ := gosperNormal_exists backend hbackend P Q hP hQ
    obtain ⟨x, hx⟩ := (normalForm_hypergeometric_iff_polynomial P Q hP hQ s hs).mp hh
    obtain ⟨c, hc, hzero, _⟩ := gosperTerm_of_solution_self backend hbackend P Q hQ s hn hs x hx
    exact ⟨c, hc, hzero⟩

/-- `ok none` certifies nonsummability; a returned result retains the residual needed
to decide whether its candidate is an antidifference. -/
theorem gosperTerm_none_not_summable_self (hbackend : backend.Valid)
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : gosperTerm backend backend some P Q = .ok none) :
    ¬Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  intro hh
  obtain ⟨c, hc, _⟩ := (gosperTerm_complete_self backend hbackend P Q hP hQ).mpr hh
  simp [h] at hc

/-- Only a negative degree bound returns `ok none`; residual consistency is left in the result. -/
theorem gosperTerm_none_iff_degreeBound_neg_self (hbackend : backend.Valid) (P Q : K[X]) :
    gosperTerm backend backend some P Q = .ok none ↔
      let s := gosperNormal backend P Q
      degreeBound s.1 (taylor (-1) s.2.1) s.2.2 < 0 := by
  rw [gosperTerm_eq_self backend hbackend]
  dsimp only
  simp only [Except.ok.injEq]
  split_ifs <;> simp_all

/-- Total correctness on nonzero inputs: coefficient descent never fails,
`ok none` proves nonsummability, while a returned result has vanishing residual
exactly when an antidifference exists.
A vanishing residual certifies the returned candidate's polynomial identity. -/
theorem gosperTerm_spec_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    match gosperTerm backend backend some P Q with
    | .error _ => False
    | .ok none => ¬Gosper.HasHypergeometricAntidifference
        (Gosper.rationalShift (-1) (toRatFunc P Q))
    | .ok (some c) =>
        ((∀ value ∈ c.residual, value = 0) ↔ Gosper.HasHypergeometricAntidifference
          (Gosper.rationalShift (-1) (toRatFunc P Q))) ∧
        ((∀ value ∈ c.residual, value = 0) → verify P Q c.numerator c.denominator = true) := by
  cases ht : gosperTerm backend backend some P Q with
  | error error =>
      rw [gosperTerm_self] at ht
      cases ht
  | ok result =>
      cases result with
      | none => exact gosperTerm_none_not_summable_self backend hbackend P Q hP hQ ht
      | some c =>
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · exact gosperTerm_hypergeometric_self backend hbackend P Q hP hQ c ht
          · intro hh
            obtain ⟨c', hc', hzero⟩ := (gosperTerm_complete_self backend hbackend P Q hP hQ).mpr hh
            have hc : c = c' := Option.some.inj (Except.ok.inj (ht.symm.trans hc'))
            simpa only [hc] using hzero
          · exact gosperTerm_verified_self backend hbackend P Q hP hQ c ht

/-- Replacing the backend preserves the existence of an output with vanishing
residual, although the returned candidate and residual array may differ. -/
theorem gosperTerm_success_iff_self (hbackend : backend.Valid) (other : Backend K)
    (hother : other.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm backend backend some P Q = .ok (some c) ∧ (∀ value ∈ c.residual, value = 0)) ↔
      ∃ c, gosperTerm other other some P Q = .ok (some c) ∧ (∀ value ∈ c.residual, value = 0) := by
  rw [gosperTerm_complete_self backend hbackend P Q hP hQ,
    gosperTerm_complete_self other hother P Q hP hQ]

/-- With a valid RREF operation, Mathlib factorization and resultant satisfy the
remaining primitive contracts, giving the hypergeometric completeness theorem. -/
theorem reference_gosperTerm_complete_self (rref : RrefOperation K)
    (hrref : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm (referenceBackend rref) (referenceBackend rref) some P Q = .ok (some c) ∧
      (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) :=
  gosperTerm_complete_self (referenceBackend rref) (referenceBackend_valid rref hrref) P Q hP hQ

end Gosper.Algorithm
