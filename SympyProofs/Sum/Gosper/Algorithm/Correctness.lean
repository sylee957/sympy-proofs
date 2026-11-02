module

public import SympyProofs.Sum.Gosper.Algorithm.Descent
public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Sum.Gosper.Rational
public import SympyProofs.Sum.Gosper.Hypergeometric

/-! Conditional soundness of successful Gosper outputs and the meaning of descent errors. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K]

theorem verify_identity [DecidableEq K] (P Q U V : K[X]) (h : verify P Q U V = true) (x : K) :
    P.eval x * U.eval (x + 1) * V.eval x -
        Q.eval x * U.eval x * V.eval (x + 1) =
      Q.eval x * V.eval x * V.eval (x + 1) := by
  have he := congrArg (fun p : K[X] => p.eval x) (verify_sound P Q U V h).2.2
  simpa only [residual, Polynomial.eval_sub, Polynomial.eval_mul, taylor_eval,
    Polynomial.eval_zero, sub_eq_zero] using he

theorem verify_at [DecidableEq K] (P Q U V : K[X]) (h : verify P Q U V = true) (x : K)
    (hQ : Q.eval x ≠ 0) (hV : V.eval x ≠ 0) (hVnext : V.eval (x + 1) ≠ 0) :
    P.eval x / Q.eval x * (U.eval (x + 1) / V.eval (x + 1)) -
      U.eval x / V.eval x = 1 := by
  have hi := verify_identity P Q U V h x
  field_simp
  linear_combination hi

def toRatFunc (U V : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) U / algebraMap K[X] (RatFunc K) V

theorem verify_ratFunc [DecidableEq K] (P Q U V : K[X]) (h : verify P Q U V = true) :
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
theorem normalForm_verify_solution_of_ratio [DecidableEq K]
    (P Q : K[X]) (hQ : Q ≠ 0) (s : K[X] × K[X] × K[X])
    (hC : s.2.2 ≠ 0) (hratio : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2))
    (x : K[X]) (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true := by
  rw [verify_iff]
  refine ⟨hQ, hC, ?_⟩
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio + (Q * taylor 1 s.2.2) * hx

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

theorem forward_iff_hypergeometric (ρ : RatFunc K) (hρ : ρ ≠ 0) :
    (∃ g : RatFunc K, ρ * Gosper.rationalShift 1 g - g = 1) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) ρ) := by
  rw [Gosper.hypergeometric_iff_rational]
  · exact forward_iff_backward ρ
  · exact fun h => hρ ((Gosper.rationalShift (-1)).injective (by simpa using h))

variable [DecidableEq K] [DecidablePred (IsInteger ℤ : K → Prop)]
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
  [DecidablePred (IsInteger ℤ : L → Prop)] [Algebra K L]
variable (backend : TermBackend K L)

private theorem gosperTerm_eq (P Q : L[X]) :
    gosperTerm backend P Q =
      match descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 with
      | none => .error .A
      | some A => match descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 with
        | none => .error .B
        | some B => .ok (gosperSolve backend.solver A (taylor (-1) B) (gosperNormal backend.normalization P Q).2.2) := by
  cases hA : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 with
  | none => simp only [gosperTerm, hA]; rfl
  | some A =>
    cases hB : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 with
    | none => simp only [gosperTerm, hA, hB]; rfl
    | some B =>
      cases hsolve : gosperSolve backend.solver A (taylor (-1) B) (gosperNormal backend.normalization P Q).2.2 <;>
        simp only [gosperTerm, hA, hB, hsolve] <;> rfl

/-- Successful descent leaves exactly the normalized solver call over `K`. -/
theorem gosperTerm_eq_of_descent (P Q : L[X]) (A B : K[X])
    (hA : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 = some A)
    (hB : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 = some B) :
    gosperTerm backend P Q =
      .ok (gosperSolve backend.solver A (taylor (-1) B) (gosperNormal backend.normalization P Q).2.2) := by
  simp [gosperTerm_eq, hA, hB]

/-- An `ok` result records successful descent of both normalized polynomials. -/
theorem gosperTerm_eq_ok_iff (P Q : L[X]) (c : Option (Result L)) :
    gosperTerm backend P Q = .ok c ↔
      ∃ A B : K[X],
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 = some A ∧
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 = some B ∧
        gosperSolve backend.solver A (taylor (-1) B) (gosperNormal backend.normalization P Q).2.2 = c := by
  cases hA : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- After successful descent, `none` is exactly the negative-degree branch. -/
theorem gosperTerm_none_iff_degreeBound_neg (hsolver : backend.solver.Valid)
    (P Q : L[X]) :
    gosperTerm backend P Q = .ok none ↔
      ∃ A B : K[X],
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 = some A ∧
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 = some B ∧
        degreeBound A (taylor (-1) B) (gosperNormal backend.normalization P Q).2.2 < 0 := by
  rw [gosperTerm_eq_ok_iff backend P Q none]
  apply exists_congr
  intro A
  apply exists_congr
  intro B
  rw [gosperSolve_eq backend.solver hsolver]
  dsimp only
  split_ifs <;> simp_all

/-- The first descent error means that the normalized `A` is not defined over `K`. -/
theorem gosperTerm_error_A_iff (hdesc : CoefficientDescentValid backend.descend)
    (P Q : L[X]) :
    gosperTerm backend P Q = .error .A ↔
      ¬∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend.normalization P Q).1 := by
  rw [← descendPolynomial_eq_none_iff backend.descend hdesc]
  cases hA : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A `B` descent error occurs only after `A` has descended successfully. -/
theorem gosperTerm_error_B_iff (hdesc : CoefficientDescentValid backend.descend)
    (P Q : L[X]) :
    gosperTerm backend P Q = .error .B ↔
      (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend.normalization P Q).1) ∧
      ¬∃ B : K[X], B.map (algebraMap K L) = (gosperNormal backend.normalization P Q).2.1 := by
  have hA : (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend.normalization P Q).1) ↔
      ∃ A, descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 = some A := by
    simp only [descendPolynomial_eq_some_iff backend.descend hdesc]
  rw [hA, ← descendPolynomial_eq_none_iff backend.descend hdesc]
  cases hA : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A vanishing residual certifies the input ratio after exact coefficient descent. -/
theorem gosperTerm_verified (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    verify P Q c.numerator c.denominator = true := by
  obtain ⟨A, B, hA, hB, hsolve⟩ :=
    (gosperTerm_eq_ok_iff backend P Q (some c)).mp h
  have hmapA := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  have hmapB' : (taylor (-1) B).map (algebraMap K L) =
      taylor (-1) (gosperNormal backend.normalization P Q).2.1 := by simp [hmapB]
  obtain ⟨x, hnum, hden, hx⟩ :=
    gosperSolve_sound backend.solver hbackend.solver A (taylor (-1) B) _ c hsolve hzero
  rw [hmapA, hmapB'] at hx
  rw [hmapB'] at hnum
  obtain ⟨hs, hratio⟩ := gosperNormal_sound backend.normalization P Q hP hQ _ rfl
  rw [hnum, hden]
  exact normalForm_verify_solution_of_ratio P Q hQ _ hs.2.2 hratio x hx

/-- Successful descent and a vanishing residual yield a rational Gosper multiplier. -/
theorem gosperTerm_sound (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc c.numerator c.denominator) -
      toRatFunc c.numerator c.denominator = 1 :=
  verify_ratFunc P Q _ _
    (gosperTerm_verified backend hbackend P Q hP hQ c h hzero)

/-- The returned multiplier satisfies its polynomial identity, including at denominator roots. -/
theorem gosperTerm_identity (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧ residual P Q c.numerator c.denominator = 0 :=
  verify_sound P Q _ _
    (gosperTerm_verified backend hbackend P Q hP hQ c h hzero)

/-- A returned multiplier with vanishing residual gives a hypergeometric antidifference. -/
theorem gosperTerm_hypergeometric (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  have hρ : toRatFunc P Q ≠ 0 := by
    unfold toRatFunc
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  exact (forward_iff_hypergeometric _ hρ).mp
    ⟨_, gosperTerm_sound backend hbackend P Q hP hQ c h hzero⟩

/-- The reconstructed forward antidifference advances by the input term. -/
theorem gosperTerm_step (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) (a : ℕ → L) (n : ℕ)
    (hQ : Q.eval (n : L) ≠ 0)
    (hV : c.denominator.eval (n : L) ≠ 0)
    (hVnext : c.denominator.eval ((n + 1 : ℕ) : L) ≠ 0)
    (hratio : a (n + 1) * Q.eval (n : L) = a n * P.eval (n : L)) :
    a (n + 1) * (c.numerator.eval ((n + 1 : ℕ) : L) /
        c.denominator.eval ((n + 1 : ℕ) : L)) -
      a n * (c.numerator.eval (n : L) / c.denominator.eval (n : L)) = a n := by
  have he := verify_at P Q c.numerator c.denominator
    (gosperTerm_verified backend hbackend P Q hP0 hQ0 c h hzero)
    (n : L) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * he

/-- The returned multiplier telescopes a finite sum under the stated denominator conditions. -/
theorem gosperTerm_sum (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0)
    (a : ℕ → L) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, Q.eval (k : L) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, c.denominator.eval (k : L) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * Q.eval (k : L) = a k * P.eval (k : L)) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * (c.numerator.eval (n : L) / c.denominator.eval (n : L)) -
        a m * (c.numerator.eval (m : L) / c.denominator.eval (m : L)) := by
  calc
    _ = ∑ k ∈ Finset.Ico m n,
        (a (k + 1) * (c.numerator.eval ((k + 1 : ℕ) : L) /
            c.denominator.eval ((k + 1 : ℕ) : L)) -
          a k * (c.numerator.eval (k : L) / c.denominator.eval (k : L))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact (gosperTerm_step backend hbackend
        P Q hP0 hQ0 c h hzero a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub
      (fun k => a k * (c.numerator.eval (k : L) / c.denominator.eval (k : L))) hmn

end Gosper.Algorithm
