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

variable [DecidableEq K]

omit [CharZero K] in
theorem NormalForm.verify_solution (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hs : s.Valid P Q) (x : K[X])
    (hx : s.A * taylor 1 x - taylor (-1) s.B * x = s.C) :
    verify P Q (taylor (-1) s.B * x) s.C = true :=
  s.verify_solution_of_ratio P Q hQ hs.1.2.2 hs.2.2 x hx

variable [DecidablePred (IsInteger ℤ : K → Prop)]

/-- A normalized polynomial solution lies within the degree bound, so applying
the generalized inverse solves its coefficient system and yields a valid certificate. -/
theorem gosperTerm_of_solution (hbackend : backend.Valid) (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hn : gosperNormal backend P Q = s) (hs : s.Valid P Q) (x : K[X])
    (hx : s.A * taylor 1 x - taylor (-1) s.B * x = s.C) :
    ∃ c, gosperTerm backend P Q = some c ∧ (∀ value ∈ c.residual, value = 0) ∧
      verify P Q c.numerator c.denominator = true := by
  subst s
  let s := gosperNormal backend P Q
  let B := taylor (-1) s.B
  let d := degreeBound s.A B s.C
  let M := coefficientSystem s.A B s.C d.toNat
  let b := toFn (equationDegree s.A B s.C d.toNat + 1) s.C
  let coeffs := (inverseRref backend.rref M).mulVec b
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx; exact hs.1.2.2 hx.symm
  have hB : B ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.1.2.1
  have hdeg := solution_degree_le s.A B s.C x hs.1.1 hB hx0 hx
  have hd : 0 ≤ d := le_trans (by omega) hdeg
  have hdn : x.natDegree ≤ d.toNat := by omega
  have hm : ∃ c, M.mulVec c = b := by
    refine ⟨toFn (d.toNat + 1) x, (coefficientSystem_correct _ _ _ _ _).mpr ?_⟩
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)]
    exact hx
  have hcoeffs : M.mulVec coeffs = b :=
    (inverseRref_solve_iff backend.rref hbackend.rref_valid M b).mpr hm
  let y := ofFn (d.toNat + 1) coeffs
  have hy : s.A * taylor 1 y - B * y = s.C :=
    (coefficientSystem_correct _ _ _ _ _).mp hcoeffs
  let r := backend.rref (augmentedIdentity M)
  have hres : r.leftResidual (r.rightMatrix.mulVec b) = 0 :=
    (r.leftResidual_eq_zero_iff M (hbackend.rref_valid _) b).mpr hcoeffs
  refine ⟨{ numerator := B * y
            denominator := s.C
            residual := r.residualEntries (r.rightMatrix.mulVec b) }, ?_, ?_, ?_⟩
  · rw [gosperTerm_eq backend hbackend]
    change (if d < 0 then none else some
      ({ numerator := B * y
         denominator := s.C
         residual := r.residualEntries (r.rightMatrix.mulVec b) } : Result K)) = _
    simp [not_lt.mpr hd]
  · exact (r.residualEntries_zero_iff (hbackend.rref_valid _) b).mpr hres
  · exact s.verify_solution P Q hQ hs y hy

/-- A returned candidate with vanishing residual exists exactly when the paper's
hypergeometric antidifference exists. The shift converts the input's forward ratio
a(n+1)/a(n) to the backward ratio a(n)/a(n-1) used by the specification. -/
theorem gosperTerm_complete (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm backend P Q = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  constructor
  · rintro ⟨c, hc, hzero⟩
    exact gosperTerm_hypergeometric backend hbackend P Q hP hQ c hc hzero
  · intro hh
    obtain ⟨s, hn, hs⟩ := gosperNormal_exists backend hbackend P Q hP hQ
    obtain ⟨x, hx⟩ := (s.hypergeometric_iff_polynomial P Q hP hQ hs).mp hh
    obtain ⟨c, hc, hzero, _⟩ := gosperTerm_of_solution backend hbackend P Q hQ s hn hs x hx
    exact ⟨c, hc, hzero⟩

/-- `none` certifies nonsummability; a returned result retains the residual needed
to decide whether its candidate is an antidifference. -/
theorem gosperTerm_none_not_summable (hbackend : backend.Valid)
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : gosperTerm backend P Q = none) :
    ¬Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  intro hh
  obtain ⟨c, hc, _⟩ := (gosperTerm_complete backend hbackend P Q hP hQ).mpr hh
  simp [h] at hc

omit [CharZero K] in
/-- Only a negative degree bound returns `none`; residual consistency is left in the result. -/
theorem gosperTerm_none_iff_degreeBound_neg (hbackend : backend.Valid) (P Q : K[X]) :
    gosperTerm backend P Q = none ↔
      let s := gosperNormal backend P Q
      degreeBound s.A (taylor (-1) s.B) s.C < 0 := by
  rw [gosperTerm_eq backend hbackend]
  dsimp only
  split_ifs <;> simp_all

/-- Total correctness on nonzero inputs: `none` proves nonsummability, while a
returned result has vanishing residual exactly when an antidifference exists.
A vanishing residual certifies the returned candidate's polynomial identity. -/
theorem gosperTerm_spec (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    match gosperTerm backend P Q with
    | none => ¬Gosper.HasHypergeometricAntidifference
        (Gosper.rationalShift (-1) (toRatFunc P Q))
    | some c =>
        ((∀ value ∈ c.residual, value = 0) ↔ Gosper.HasHypergeometricAntidifference
          (Gosper.rationalShift (-1) (toRatFunc P Q))) ∧
        ((∀ value ∈ c.residual, value = 0) → verify P Q c.numerator c.denominator = true) := by
  cases ht : gosperTerm backend P Q with
  | none => exact gosperTerm_none_not_summable backend hbackend P Q hP hQ ht
  | some c =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact gosperTerm_hypergeometric backend hbackend P Q hP hQ c ht
    · intro hh
      obtain ⟨c', hc', hzero⟩ := (gosperTerm_complete backend hbackend P Q hP hQ).mpr hh
      have hc : c = c' := Option.some.inj (ht.symm.trans hc')
      simpa only [hc] using hzero
    · exact gosperTerm_verified backend hbackend P Q hP hQ c ht

/-- Replacing the backend preserves the existence of an output with vanishing
residual, although the returned candidate and residual array may differ. -/
theorem gosperTerm_success_iff (hbackend : backend.Valid) (other : Backend K)
    (hother : other.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm backend P Q = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      ∃ c, gosperTerm other P Q = some c ∧ (∀ value ∈ c.residual, value = 0) := by
  rw [gosperTerm_complete backend hbackend P Q hP hQ,
    gosperTerm_complete other hother P Q hP hQ]

/-- With a valid RREF operation, Mathlib factorization and resultant satisfy the
remaining primitive contracts, giving the hypergeometric completeness theorem. -/
theorem reference_gosperTerm_complete (rref : RrefOperation K)
    (hrref : ∀ {m n} (A : Matrix (Fin m) (Fin n) K), (rref A).Valid A)
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ c, gosperTerm (referenceBackend rref) P Q = some c ∧ (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) :=
  gosperTerm_complete (referenceBackend rref) (referenceBackend_valid rref hrref) P Q hP hQ

end Gosper.Algorithm
