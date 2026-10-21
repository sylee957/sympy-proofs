module

public import SympyProofs.Gosper.Algorithm.Correctness
public import SympyProofs.Gosper.Algorithm.NormalizationCorrectness

/-! Completeness of normalization, bounded solving, and Gosper reconstruction. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

local instance completenessDecidableEq : DecidableEq K := Classical.decEq K

theorem solvePolynomial_complete (A B C : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (∃ x, solvePolynomial A B C = some x) ↔
      ∃ x : K[X], A * taylor 1 x - B * x = C := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, solvePolynomial_sound A B C x hx⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx; exact hC hx.symm
    have hdeg := solution_degree_le A B C x hA hB hx0 hx
    have hd : 0 ≤ degreeBound A B C := le_trans (by omega) hdeg
    have hdn : x.natDegree ≤ (degreeBound A B C).toNat := by omega
    have hm : ∃ c, (coefficientSystem A B C (degreeBound A B C).toNat).mulVec c =
        toFn (equationDegree A B C (degreeBound A B C).toNat + 1) C := by
      refine ⟨toFn ((degreeBound A B C).toNat + 1) x, (coefficientSystem_correct _ _ _ _ _).mpr ?_⟩
      rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
      exact hx
    obtain ⟨c, hc⟩ := (solveLinear_complete _ _).mpr hm
    refine ⟨ofFn ((degreeBound A B C).toNat + 1) c, ?_⟩
    simp [solvePolynomial, not_lt.mpr hd, hc]

theorem solvePolynomial_none_iff (A B C : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    solvePolynomial A B C = none ↔ ¬∃ x : K[X], A * taylor 1 x - B * x = C := by
  rw [← solvePolynomial_complete A B C hA hB hC]
  cases solvePolynomial A B C <;> simp

omit [CharZero K] in
theorem NormalForm.backwardRatio (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hs : s.Valid P Q) :
    Gosper.rationalShift (-1) (toRatFunc P Q) =
      Gosper.normalRatio s.C (taylor (-1) s.A) (taylor (-1) s.B) := by
  let ι := algebraMap K[X] (RatFunc K)
  have hq : ι (taylor (-1) Q) ≠ 0 := by simpa [ι] using hQ
  have hd : ι (taylor (-1) s.C * taylor (-1) s.B) ≠ 0 := by
    simpa [ι] using mul_ne_zero hs.1.2.2 hs.1.2.1
  simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial, Gosper.normalRatio]
  apply (div_eq_div_iff hq hd).mpr
  have he := congrArg (taylor (-1)) hs.2.2
  simp only [taylor_mul, taylor_taylor, neg_add_cancel, taylor_zero] at he
  simpa only [ι, ← map_mul, mul_assoc, mul_comm, mul_left_comm] using congrArg ι he

theorem NormalForm.hypergeometric_iff_polynomial (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (s : NormalForm K) (hs : s.Valid P Q) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) ↔
      ∃ x : K[X], s.A * taylor 1 x - taylor (-1) s.B * x = s.C := by
  have hρ : Gosper.rationalShift (-1) (toRatFunc P Q) ≠ 0 := by
    simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial]
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  have hA : taylor (-1 : K) s.A ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.1
  have hB : taylor (-1 : K) s.B ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.2.1
  have hcop : Gosper.ShiftCoprime (taylor (-1) s.A) (taylor (-1) s.B) := by
    intro j
    simpa [taylor_taylor, add_comm] using (hs.2.1 j).map (taylorAlgHom (-1 : K)).toRingHom
  rw [Gosper.hypergeometric_iff_rational _ hρ, NormalForm.backwardRatio P Q hQ s hs,
    Gosper.summable_iff_rational_solution _ _ _ hs.1.2.2 hA hB,
    Gosper.rational_solution_iff_polynomial _ _ _ hcop]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨taylor (-1) f, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hf
  · rintro ⟨x, hx⟩
    refine ⟨taylor 1 x, ?_⟩
    simpa [Gosper.operator_apply, taylor_taylor] using hx

omit [CharZero K] in
theorem NormalForm.verify_solution (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hs : s.Valid P Q) (x : K[X])
    (hx : s.A * taylor 1 x - taylor (-1) s.B * x = s.C) :
    verify P Q (taylor (-1) s.B * x) s.C = true :=
  s.verify_solution_of_ratio P Q hQ hs.1.2.2 hs.2.2 x hx

omit [CharZero K] in
/-- A normalized polynomial solution reconstructs a valid certificate. -/
theorem gosperTerm_of_solution (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hn : gosperNormal P Q = s) (hs : s.Valid P Q) (x : K[X])
    (hx : solvePolynomial s.A (taylor (-1) s.B) s.C = some x) :
    ∃ c, gosperTerm P Q = some c ∧ verify P Q c.numerator c.denominator = true :=
  gosperTerm_of_normalized_solution P Q hQ s hn hs.1.2.2 hs.2.2 x hx

/-- Total correctness on nonzero input polynomials: the procedure either
returns a valid certificate or proves that no hypergeometric antidifference
exists. Totality is guaranteed by the definition's return type. -/
theorem gosperTerm_spec (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    match gosperTerm P Q with
    | none => ¬Gosper.HasHypergeometricAntidifference
        (Gosper.rationalShift (-1) (toRatFunc P Q))
    | some c => verify P Q c.numerator c.denominator = true := by
  obtain ⟨s, hn, hs⟩ := gosperNormal_exists P Q hP hQ
  cases hr : solvePolynomial s.A (taylor (-1) s.B) s.C with
  | none =>
    have ht : gosperTerm P Q = none := by simp [gosperTerm, hn, hr]
    rw [ht]
    rw [s.hypergeometric_iff_polynomial P Q hP hQ hs]
    exact (solvePolynomial_none_iff _ _ _ hs.1.1
      ((taylor_eq_zero _ _).not.mpr hs.1.2.1) hs.1.2.2).mp hr
  | some x =>
    obtain ⟨c, hc, hv⟩ := gosperTerm_of_solution P Q hQ s hn hs x hr
    simpa [hc] using hv

/-- The modeled algorithm succeeds exactly when the paper's hypergeometric
antidifference exists. The shift converts the input's forward ratio a(n+1)/a(n)
to the backward ratio a(n)/a(n-1) used by the mathematical specification. -/
theorem gosperTerm_complete (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm P Q = some c) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  constructor
  · rintro ⟨c, hc⟩
    exact gosperTerm_hypergeometric P Q hP hQ c hc
  · intro hh
    have hs := gosperTerm_spec P Q hP hQ
    cases hr : gosperTerm P Q with
    | none =>
      simp only [hr] at hs
      exact (hs hh).elim
    | some c => exact ⟨c, rfl⟩

/-- Returning `none` is a certified nonsummability result, not a solver failure. -/
theorem gosperTerm_none_iff (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    gosperTerm P Q = none ↔
      ¬Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  rw [← gosperTerm_complete P Q hP hQ]
  cases gosperTerm P Q <;> simp

end Gosper.Algorithm
