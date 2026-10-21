module

public import SympyProofs.Gosper.Algorithm.Algorithm
public import SympyProofs.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Gosper.Rational
public import SympyProofs.Gosper.Hypergeometric

/-!
# Soundness over the coefficient field

The algorithm works directly with Mathlib polynomials. Its normalization,
polynomial solving, and reconstruction steps prove the returned certificate's
identity without a runtime check. Evaluation at a particular index has explicit
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
theorem NormalForm.verify_solution_of_ratio (P Q : K[X]) (hQ : Q ≠ 0) (s : NormalForm K)
    (hC : s.C ≠ 0) (hratio : P * (s.B * s.C) = Q * (s.A * taylor 1 s.C))
    (x : K[X]) (hx : s.A * taylor 1 x - taylor (-1) s.B * x = s.C) :
    verify P Q (taylor (-1) s.B * x) s.C = true := by
  rw [verify_iff]
  refine ⟨hQ, hC, ?_⟩
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio + (Q * taylor 1 s.C) * hx

variable [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- Every certificate constructed by `gosperTerm` satisfies the original equation.
This follows from the algorithm's steps, independently of running `verify`. -/
theorem gosperTerm_verified (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) : verify P Q c.numerator c.denominator = true := by
  let s := gosperNormal backend P Q
  let B := taylor (-1) s.B
  let d := degreeBound s.A B s.C
  let M := coefficientSystem s.A B s.C d.toNat
  let b := toFn (equationDegree s.A B s.C d.toNat + 1) s.C
  let r := backend.rref (augmented M b)
  let x := ofFn (d.toNat + 1) r.solution
  change (if d < 0 then none else if Fin.last (d.toNat + 1) ∈ r.pivots then none
    else some (⟨B * x, s.C⟩ : Certificate K)) = some c at h
  split_ifs at h with hd hp
  cases Option.some.inj h
  have hx : s.A * taylor 1 x - B * x = s.C :=
    (coefficientSystem_correct _ _ _ _ _).mp
      (RrefResult.solution_correct M b r (hbackend.rref_valid _) hp)
  obtain ⟨hs, hratio⟩ := gosperNormal_sound backend P Q hP hQ s rfl
  exact s.verify_solution_of_ratio P Q hQ hs.2.2 hratio x hx

/-- Every successful execution supplies a rational Gosper multiplier. -/
theorem gosperTerm_sound (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc c.numerator c.denominator) -
      toRatFunc c.numerator c.denominator = 1 :=
  verify_ratFunc P Q _ _ (gosperTerm_verified backend hbackend P Q hP hQ c h)

/-- The polynomial identity holds even at roots of its denominators; dividing
after specialization instead requires the hypotheses of `verify_at`. -/
theorem gosperTerm_identity (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧ residual P Q c.numerator c.denominator = 0 :=
  verify_sound P Q _ _ (gosperTerm_verified backend hbackend P Q hP hQ c h)

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

/-- A returned certificate implies a hypergeometric antidifference for the
paper's backward term ratio, provided the input numerator is nonzero. -/
theorem gosperTerm_hypergeometric (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  have hρ : toRatFunc P Q ≠ 0 := by
    unfold toRatFunc
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  exact (forward_iff_hypergeometric _ hρ).mp ⟨_, gosperTerm_sound backend hbackend P Q hP hQ c h⟩

/-- The forward antidifference reconstructed from the returned multiplier. -/
def certificateValue (a : ℕ → K) (c : Certificate K) (n : ℕ) : K :=
  a n * (c.numerator.eval (n : K) / c.denominator.eval (n : K))

theorem gosperTerm_step (hbackend : backend.Valid) (P Q : K[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) (a : ℕ → K) (n : ℕ)
    (hQ : Q.eval (n : K) ≠ 0)
    (hV : c.denominator.eval (n : K) ≠ 0)
    (hVnext : c.denominator.eval ((n + 1 : ℕ) : K) ≠ 0)
    (hratio : a (n + 1) * Q.eval (n : K) = a n * P.eval (n : K)) :
    certificateValue a c (n + 1) - certificateValue a c n = a n := by
  have he := verify_at P Q c.numerator c.denominator (gosperTerm_verified backend hbackend P Q hP0 hQ0 c h)
    (n : K) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [certificateValue, Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * he

/-- A finite sum on [m,n), with denominator assumptions only on that interval
and its endpoints. No nonvanishing assumption on the terms a(k) is needed. -/
theorem gosperTerm_sum (hbackend : backend.Valid) (P Q : K[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Certificate K)
    (h : gosperTerm backend P Q = some c) (a : ℕ → K) (m n : ℕ) (hmn : m ≤ n)
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
      exact (gosperTerm_step backend hbackend P Q hP0 hQ0 c h a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub _ hmn

end Gosper.Algorithm
