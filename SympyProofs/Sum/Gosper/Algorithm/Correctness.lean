module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm
public import SympyProofs.Sum.Gosper.Algorithm.Descent
public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Sum.Gosper.Backend.Vector
public import SympyProofs.Sum.Gosper.Backend.Matrix
public import SympyProofs.Sum.Gosper.Backend.Residual
public import SympyProofs.Sum.Gosper.Rational
public import SympyProofs.Sum.Gosper.Hypergeometric

/-!
# Soundness over the coefficient field

The algorithm works directly with Mathlib polynomials. Its normalization and
reconstruction steps prove the returned candidate's identity when its residual
vanishes. Evaluation at a particular index has explicit
denominator conditions, separate from equality in the rational-function field.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [DecidableEq K]
variable (backend : Backend K)

theorem verify_identity (P Q U V : K[X]) (h : verify P Q U V = true) (x : K) :
    P.eval x * U.eval (x + 1) * V.eval x -
        Q.eval x * U.eval x * V.eval (x + 1) =
      Q.eval x * V.eval x * V.eval (x + 1) := by
  have he := congrArg (fun p : K[X] => p.eval x) (verify_sound P Q U V h).2.2
  simpa only [residual, Polynomial.eval_sub, Polynomial.eval_mul, taylor_eval,
    Polynomial.eval_zero, sub_eq_zero] using he

theorem verify_at (P Q U V : K[X]) (h : verify P Q U V = true) (x : K)
    (hQ : Q.eval x ≠ 0) (hV : V.eval x ≠ 0) (hVnext : V.eval (x + 1) ≠ 0) :
    P.eval x / Q.eval x * (U.eval (x + 1) / V.eval (x + 1)) -
      U.eval x / V.eval x = 1 := by
  have hi := verify_identity P Q U V h x
  field_simp
  linear_combination hi

def toRatFunc (U V : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) U / algebraMap K[X] (RatFunc K) V

theorem verify_ratFunc (P Q U V : K[X]) (h : verify P Q U V = true) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc U V) - toRatFunc U V = 1 := by
  obtain ⟨hQ, hV, he⟩ := verify_sound P Q U V h
  let ι := algebraMap K[X] (RatFunc K)
  have map_ne (p : K[X]) (hp : p ≠ 0) : ι p ≠ 0 := by
    intro hz
    exact hp ((IsFractionRing.injective K[X] (RatFunc K)) (by simpa [ι] using hz))
  have hq := map_ne _ hQ
  have hv := map_ne _ hV
  have hsv := map_ne _ ((taylor_eq_zero 1 V).not.mpr hV)
  have hm := congrArg ι he
  simp only [residual, map_sub, map_mul, map_zero] at hm
  simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial]
  change ι P / ι Q * (ι (taylor 1 U) / ι (taylor 1 V)) - ι U / ι V = 1
  field_simp
  linear_combination hm

/-- The normalized equation and ratio identity imply the certificate identity;
shift-coprimality is not needed for this direction. -/
theorem normalForm_verify_solution_of_ratio (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hC : s.2.2 ≠ 0) (hratio : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2))
    (x : K[X]) (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true := by
  rw [verify_iff]
  refine ⟨hQ, hC, ?_⟩
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio + (Q * taylor 1 s.2.2) * hx

variable [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- The inline identity augmentation, coefficient vector, and residual array
implement the coefficient-system specification. -/
theorem gosperTerm_eq_self (hbackend : backend.Valid) (P Q : K[X]) :
    gosperTerm backend backend some P Q = .ok (
      let s := gosperNormal backend P Q
      let B := taylor (-1) s.2.1
      let d := degreeBound s.1 B s.2.2
      if d < 0 then none else
        let M := coefficientSystem s.1 B s.2.2 d.toNat
        let b := toFn (max s.2.2.natDegree (max s.1.natDegree B.natDegree + d.toNat) + 1) s.2.2
        let r := backend.rref (augmentedIdentity M)
        let U := inverseRref backend.rref M
        let coeffs := U.mulVec b
        some { numerator := B * ofFn (d.toNat + 1) coeffs
               denominator := s.2.2
               residual := r.residualEntries (r.rightMatrix.mulVec b) }) := by
  rw [gosperTerm_self]
  rw [gosperSolve_eq backend hbackend]
  simp only [Algebra.algebraMap_self, Polynomial.map_id,
    ← Polynomial.ofFn_eq_sum_monomial]
  rfl

/-- A returned candidate with vanishing residual satisfies the original equation.
This follows from the algorithm's steps, independently of running `verify`. -/
theorem gosperTerm_verified_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0) :
    verify P Q c.numerator c.denominator = true := by
  rw [gosperTerm_eq_self backend hbackend] at h
  have h := Except.ok.inj h
  let s := gosperNormal backend P Q
  let B := taylor (-1) s.2.1
  let d := degreeBound s.1 B s.2.2
  let M := coefficientSystem s.1 B s.2.2 d.toNat
  let b := toFn (max s.2.2.natDegree (max s.1.natDegree B.natDegree + d.toNat) + 1) s.2.2
  let r := backend.rref (augmentedIdentity M)
  let coeffs := (inverseRref backend.rref M).mulVec b
  let x := ofFn (d.toNat + 1) coeffs
  change (if d < 0 then none else some
    ({ numerator := B * x
       denominator := s.2.2
       residual := r.residualEntries (r.rightMatrix.mulVec b) } : Result K)) = some c at h
  split_ifs at h with hd
  cases Option.some.inj h
  have hresidual : r.leftResidual (r.rightMatrix.mulVec b) = 0 :=
    (r.residualEntries_zero_iff (hbackend.rref_valid _) b).mp hzero
  have hcoeffs : M.mulVec coeffs = b :=
    (RrefResult.leftResidual_eq_zero_iff M r (hbackend.rref_valid _) b).mp hresidual
  have hx : s.1 * taylor 1 x - B * x = s.2.2 :=
    (coefficientSystem_correct _ _ _ _ _).mp hcoeffs
  obtain ⟨hs, hratio⟩ := gosperNormal_sound backend P Q hP hQ s rfl
  exact normalForm_verify_solution_of_ratio P Q hQ s hs.2.2 hratio x hx

/-- A returned candidate with vanishing residual supplies a rational Gosper multiplier. -/
theorem gosperTerm_sound_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc c.numerator c.denominator) -
      toRatFunc c.numerator c.denominator = 1 :=
  verify_ratFunc P Q _ _ (gosperTerm_verified_self backend hbackend P Q hP hQ c h hzero)

/-- The polynomial identity holds even at roots of its denominators; dividing
after specialization instead requires the hypotheses of `verify_at`. -/
theorem gosperTerm_identity_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧
      residual P Q c.numerator c.denominator = 0 :=
  verify_sound P Q _ _ (gosperTerm_verified_self backend hbackend P Q hP hQ c h hzero)

omit [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)] [DecidableEq K] in
/-- Translate the forward multiplier equation to the paper's backward ratio.
The paper's multiplier is `g + 1`. -/
theorem forward_iff_backward (ρ : RatFunc K) :
    (∃ g : RatFunc K, ρ * Gosper.rationalShift 1 g - g = 1) ↔
      Gosper.HasRationalAntidifference (Gosper.rationalShift (-1) ρ) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g + 1, ?_⟩
    have hs := congrArg (Gosper.rationalShift (-1)) hg
    simp only [map_sub, map_mul, map_one, Gosper.rationalShift_add,
      neg_add_cancel, Gosper.rationalShift_zero] at hs
    simp only [map_add, map_one]
    linear_combination hs
  · rintro ⟨g, hg⟩
    refine ⟨g - 1, ?_⟩
    have hs := congrArg (Gosper.rationalShift 1) hg
    simp only [map_sub, map_mul, Gosper.rationalShift_add, add_neg_cancel,
      Gosper.rationalShift_zero] at hs
    simp only [map_sub, map_one]
    linear_combination hs

omit [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)] [DecidableEq K] in
theorem forward_iff_hypergeometric (ρ : RatFunc K) (hρ : ρ ≠ 0) :
    (∃ g : RatFunc K, ρ * Gosper.rationalShift 1 g - g = 1) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) ρ) := by
  rw [Gosper.hypergeometric_iff_rational]
  · exact forward_iff_backward ρ
  · exact fun h => hρ ((Gosper.rationalShift (-1)).injective (by simpa using h))

/-- A returned candidate with vanishing residual implies a hypergeometric antidifference
for the paper's backward term ratio, provided the input numerator is nonzero. -/
theorem gosperTerm_hypergeometric_self (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  have hρ : toRatFunc P Q ≠ 0 := by
    unfold toRatFunc
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  exact (forward_iff_hypergeometric _ hρ).mp ⟨_, gosperTerm_sound_self backend hbackend P Q hP hQ c h hzero⟩

/-- The forward antidifference reconstructed from the returned multiplier. -/
def certificateValue (a : ℕ → K) (c : Result K) (n : ℕ) : K :=
  a n * (c.numerator.eval (n : K) / c.denominator.eval (n : K))

theorem gosperTerm_step_self (hbackend : backend.Valid) (P Q : K[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0) (a : ℕ → K) (n : ℕ)
    (hQ : Q.eval (n : K) ≠ 0)
    (hV : c.denominator.eval (n : K) ≠ 0)
    (hVnext : c.denominator.eval ((n + 1 : ℕ) : K) ≠ 0)
    (hratio : a (n + 1) * Q.eval (n : K) = a n * P.eval (n : K)) :
    certificateValue a c (n + 1) - certificateValue a c n = a n := by
  have he := verify_at P Q c.numerator c.denominator
    (gosperTerm_verified_self backend hbackend P Q hP0 hQ0 c h hzero)
    (n : K) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [certificateValue, Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * he

/-- A finite sum on [m,n), with denominator assumptions only on that interval
and its endpoints. No nonvanishing assumption on the terms a(k) is needed. -/
theorem gosperTerm_sum_self (hbackend : backend.Valid) (P Q : K[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result K)
    (h : gosperTerm backend backend some P Q = .ok (some c)) (hzero : ∀ value ∈ c.residual, value = 0)
    (a : ℕ → K) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, Q.eval (k : K) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, c.denominator.eval (k : K) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * Q.eval (k : K) = a k * P.eval (k : K)) :
    ∑ k ∈ Finset.Ico m n, a k = certificateValue a c n - certificateValue a c m := by
  calc
    _ = ∑ k ∈ Finset.Ico m n, (certificateValue a c (k + 1) - certificateValue a c k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact (gosperTerm_step_self backend hbackend P Q hP0 hQ0 c h hzero a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub _ hmn

end Gosper.Algorithm
