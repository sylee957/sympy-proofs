module

public import SympyProofs.Sum.Gosper.Algorithm.Descent
public import SympyProofs.Sum.Gosper.Algorithm.Completeness

/-! Correctness of normalization over an extension followed by coefficient descent. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K L : Type} [Field K] [DecidableEq K]
variable [DecidablePred (IsInteger ℤ : K → Prop)]
variable [Field L] [CharZero L] [DecidableEq L]
variable [DecidablePred (IsInteger ℤ : L → Prop)] [Algebra K L]
variable (backendL : Backend L) (backendK : Backend K) (descendCoeff : L → Option K)

private theorem gosperTerm_eq (P Q : L[X]) :
    gosperTerm backendL backendK descendCoeff P Q =
      match descendPolynomial descendCoeff (gosperNormal backendL P Q).1 with
      | none => .error .A
      | some A => match descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 with
        | none => .error .B
        | some B => .ok (gosperSolve backendK A (taylor (-1) B) (gosperNormal backendL P Q).2.2) := by
  cases hA : descendPolynomial descendCoeff (gosperNormal backendL P Q).1 with
  | none => simp only [gosperTerm, hA]; rfl
  | some A =>
    cases hB : descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 with
    | none => simp only [gosperTerm, hA, hB]; rfl
    | some B =>
      cases hsolve : gosperSolve backendK A (taylor (-1) B) (gosperNormal backendL P Q).2.2 <;>
        simp only [gosperTerm, hA, hB, hsolve] <;> rfl

/-- Successful descent leaves exactly the normalized solver call over `K`. -/
theorem gosperTerm_eq_of_descent (P Q : L[X]) (A B : K[X])
    (hA : descendPolynomial descendCoeff (gosperNormal backendL P Q).1 = some A)
    (hB : descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 = some B) :
    gosperTerm backendL backendK descendCoeff P Q =
      .ok (gosperSolve backendK A (taylor (-1) B) (gosperNormal backendL P Q).2.2) := by
  simp [gosperTerm_eq, hA, hB]

/-- An `ok` result records successful descent of both normalized polynomials. -/
theorem gosperTerm_eq_ok_iff (P Q : L[X]) (c : Option (Result L)) :
    gosperTerm backendL backendK descendCoeff P Q = .ok c ↔
      ∃ A B : K[X],
        descendPolynomial descendCoeff (gosperNormal backendL P Q).1 = some A ∧
        descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 = some B ∧
        gosperSolve backendK A (taylor (-1) B) (gosperNormal backendL P Q).2.2 = c := by
  cases hA : descendPolynomial descendCoeff (gosperNormal backendL P Q).1 <;>
    cases hB : descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- After successful descent, `none` is exactly the negative-degree branch. -/
theorem gosperTerm_none_iff_degreeBound_neg (hbackendK : backendK.Valid)
    (P Q : L[X]) :
    gosperTerm backendL backendK descendCoeff P Q = .ok none ↔
      ∃ A B : K[X],
        descendPolynomial descendCoeff (gosperNormal backendL P Q).1 = some A ∧
        descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 = some B ∧
        degreeBound A (taylor (-1) B) (gosperNormal backendL P Q).2.2 < 0 := by
  rw [gosperTerm_eq_ok_iff backendL backendK descendCoeff P Q none]
  apply exists_congr
  intro A
  apply exists_congr
  intro B
  rw [gosperSolve_eq backendK hbackendK]
  dsimp only
  split_ifs <;> simp_all

/-- The first descent error means that the normalized `A` is not defined over `K`. -/
theorem gosperTerm_error_A_iff (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) :
    gosperTerm backendL backendK descendCoeff P Q = .error .A ↔
      ¬∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backendL P Q).1 := by
  rw [← descendPolynomial_eq_none_iff descendCoeff hdesc]
  cases hA : descendPolynomial descendCoeff (gosperNormal backendL P Q).1 <;>
    cases hB : descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A `B` descent error occurs only after `A` has descended successfully. -/
theorem gosperTerm_error_B_iff (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) :
    gosperTerm backendL backendK descendCoeff P Q = .error .B ↔
      (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backendL P Q).1) ∧
      ¬∃ B : K[X], B.map (algebraMap K L) = (gosperNormal backendL P Q).2.1 := by
  have hA : (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backendL P Q).1) ↔
      ∃ A, descendPolynomial descendCoeff (gosperNormal backendL P Q).1 = some A := by
    simp only [descendPolynomial_eq_some_iff descendCoeff hdesc]
  rw [hA, ← descendPolynomial_eq_none_iff descendCoeff hdesc]
  cases hA : descendPolynomial descendCoeff (gosperNormal backendL P Q).1 <;>
    cases hB : descendPolynomial descendCoeff (gosperNormal backendL P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A vanishing residual certifies the input ratio after exact coefficient descent. -/
theorem gosperTerm_verified (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    verify P Q c.numerator c.denominator = true := by
  obtain ⟨A, B, hA, hB, hsolve⟩ :=
    (gosperTerm_eq_ok_iff backendL backendK descendCoeff P Q (some c)).mp h
  have hmapA := (descendPolynomial_eq_some_iff descendCoeff hdesc _ A).mp hA
  have hmapB := (descendPolynomial_eq_some_iff descendCoeff hdesc _ B).mp hB
  have hmapB' : (taylor (-1) B).map (algebraMap K L) =
      taylor (-1) (gosperNormal backendL P Q).2.1 := by simp [hmapB]
  obtain ⟨x, hnum, hden, hx⟩ :=
    gosperSolve_sound backendK hbackendK A (taylor (-1) B) _ c hsolve hzero
  rw [hmapA, hmapB'] at hx
  rw [hmapB'] at hnum
  obtain ⟨hs, hratio⟩ := gosperNormal_sound backendL P Q hP hQ _ rfl
  rw [hnum, hden]
  exact normalForm_verify_solution_of_ratio P Q hQ _ hs.2.2 hratio x hx

/-- Successful descent and a vanishing residual yield a rational Gosper multiplier. -/
theorem gosperTerm_sound (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc c.numerator c.denominator) -
      toRatFunc c.numerator c.denominator = 1 :=
  verify_ratFunc P Q _ _
    (gosperTerm_verified backendL backendK descendCoeff hbackendK hdesc P Q hP hQ c h hzero)

/-- The returned multiplier satisfies its polynomial identity, including at denominator roots. -/
theorem gosperTerm_identity (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧ residual P Q c.numerator c.denominator = 0 :=
  verify_sound P Q _ _
    (gosperTerm_verified backendL backendK descendCoeff hbackendK hdesc P Q hP hQ c h hzero)

/-- A returned multiplier with vanishing residual gives a hypergeometric antidifference. -/
theorem gosperTerm_hypergeometric (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  have hρ : toRatFunc P Q ≠ 0 := by
    unfold toRatFunc
    exact div_ne_zero (by simpa using hP) (by simpa using hQ)
  exact (forward_iff_hypergeometric _ hρ).mp
    ⟨_, gosperTerm_sound backendL backendK descendCoeff hbackendK hdesc P Q hP hQ c h hzero⟩

/-- The reconstructed forward antidifference advances by the input term. -/
theorem gosperTerm_step (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) (a : ℕ → L) (n : ℕ)
    (hQ : Q.eval (n : L) ≠ 0)
    (hV : c.denominator.eval (n : L) ≠ 0)
    (hVnext : c.denominator.eval ((n + 1 : ℕ) : L) ≠ 0)
    (hratio : a (n + 1) * Q.eval (n : L) = a n * P.eval (n : L)) :
    certificateValue a c (n + 1) - certificateValue a c n = a n := by
  have he := verify_at P Q c.numerator c.denominator
    (gosperTerm_verified backendL backendK descendCoeff hbackendK hdesc P Q hP0 hQ0 c h hzero)
    (n : L) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [certificateValue, Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * he

/-- The returned multiplier telescopes a finite sum under the stated denominator conditions. -/
theorem gosperTerm_sum (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0)
    (a : ℕ → L) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, Q.eval (k : L) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, c.denominator.eval (k : L) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * Q.eval (k : L) = a k * P.eval (k : L)) :
    ∑ k ∈ Finset.Ico m n, a k = certificateValue a c n - certificateValue a c m := by
  calc
    _ = ∑ k ∈ Finset.Ico m n, (certificateValue a c (k + 1) - certificateValue a c k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact (gosperTerm_step backendL backendK descendCoeff hbackendK hdesc
        P Q hP0 hQ0 c h hzero a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub _ hmn

variable [CharZero K]

/-- When both normalized polynomials descend, solving over `K` is complete over `L`. -/
theorem gosperTerm_complete (hbackendL : backendL.Valid) (hbackendK : backendK.Valid)
    (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hA : (gosperNormal backendL P Q).1 ∈ Polynomial.lifts (algebraMap K L))
    (hB : (gosperNormal backendL P Q).2.1 ∈ Polynomial.lifts (algebraMap K L)) :
    (∃ c, gosperTerm backendL backendK descendCoeff P Q = .ok (some c) ∧
      (∀ value ∈ c.residual, value = 0)) ↔
      Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  obtain ⟨A, hA⟩ := (descendPolynomial_exists_iff descendCoeff hdesc _).mpr hA
  obtain ⟨B, hB⟩ := (descendPolynomial_exists_iff descendCoeff hdesc _).mpr hB
  have hmapA := (descendPolynomial_eq_some_iff descendCoeff hdesc _ A).mp hA
  have hmapB := (descendPolynomial_eq_some_iff descendCoeff hdesc _ B).mp hB
  have hmapB' : (taylor (-1) B).map (algebraMap K L) =
      taylor (-1) (gosperNormal backendL P Q).2.1 := by simp [hmapB]
  obtain ⟨s, hs, hvalid⟩ := gosperNormal_exists backendL hbackendL P Q hP hQ
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
  rw [gosperTerm_eq_of_descent backendL backendK descendCoeff P Q A B hA hB]
  simp only [Except.ok.injEq]
  rw [gosperSolve_complete backendK hbackendK A (taylor (-1) B) _ hA0 hBshift hvalid.1.2.2]
  rw [hmapA, hmapB']
  exact (normalForm_hypergeometric_iff_polynomial P Q hP hQ _ hvalid).symm

/-- `ok none` means nonsummability, rather than a failed coefficient descent. -/
theorem gosperTerm_none_not_summable (hbackendL : backendL.Valid)
    (hbackendK : backendK.Valid) (hdesc : CoefficientDescentValid descendCoeff)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : gosperTerm backendL backendK descendCoeff P Q = .ok none) :
    ¬Gosper.HasHypergeometricAntidifference (Gosper.rationalShift (-1) (toRatFunc P Q)) := by
  obtain ⟨A, B, hA, hB, _⟩ :=
    (gosperTerm_eq_ok_iff backendL backendK descendCoeff P Q none).mp h
  have hAlift := (descendPolynomial_exists_iff descendCoeff hdesc _).mp ⟨A, hA⟩
  have hBlift := (descendPolynomial_exists_iff descendCoeff hdesc _).mp ⟨B, hB⟩
  intro hh
  obtain ⟨c, hc, _⟩ :=
    (gosperTerm_complete backendL backendK descendCoeff hbackendL hbackendK hdesc
      P Q hP hQ hAlift hBlift).mpr hh
  simp [h] at hc

end Gosper.Algorithm
