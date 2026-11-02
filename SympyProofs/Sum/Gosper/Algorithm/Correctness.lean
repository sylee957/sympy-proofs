module

public import SympyProofs.Sum.Gosper.Algorithm.Descent
public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationSpecialization
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Sum.Gosper.Rational
public import SympyProofs.Sum.Gosper.Hypergeometric

/-! Conditional soundness of successful Gosper outputs and the meaning of descent errors. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {F : Type} [Field F]

theorem verify_identity [DecidableEq F] (P Q U V : F[X]) (h : verify P Q U V = true) (x : F) :
    P.eval x * U.eval (x + 1) * V.eval x -
        Q.eval x * U.eval x * V.eval (x + 1) =
      Q.eval x * V.eval x * V.eval (x + 1) := by
  have he := congrArg (fun p : F[X] => p.eval x) (verify_sound P Q U V h).2.2
  simpa only [residual, Polynomial.eval_sub, Polynomial.eval_mul, taylor_eval,
    Polynomial.eval_zero, sub_eq_zero] using he

theorem verify_at [DecidableEq F] (P Q U V : F[X]) (h : verify P Q U V = true) (x : F)
    (hQ : Q.eval x ≠ 0) (hV : V.eval x ≠ 0) (hVnext : V.eval (x + 1) ≠ 0) :
    P.eval x / Q.eval x * (U.eval (x + 1) / V.eval (x + 1)) -
      U.eval x / V.eval x = 1 := by
  have hi := verify_identity P Q U V h x
  field_simp
  linear_combination hi

def toRatFunc (U V : F[X]) : RatFunc F :=
  algebraMap F[X] (RatFunc F) U / algebraMap F[X] (RatFunc F) V

theorem toRatFunc_ne_zero (U V : F[X]) (hU : U ≠ 0) (hV : V ≠ 0) :
    toRatFunc U V ≠ 0 := by
  unfold toRatFunc
  exact div_ne_zero (by simpa using hU) (by simpa using hV)

theorem verify_ratFunc [DecidableEq F] (P Q U V : F[X]) (h : verify P Q U V = true) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc U V) - toRatFunc U V = 1 := by
  obtain ⟨hQ, hV, he⟩ := verify_sound P Q U V h
  let ι := algebraMap F[X] (RatFunc F)
  have map_ne (p : F[X]) (hp : p ≠ 0) : ι p ≠ 0 := by
    intro hz
    exact hp ((IsFractionRing.injective F[X] (RatFunc F)) (by simpa [ι] using hz))
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
theorem normalForm_verify_solution_of_ratio [DecidableEq F]
    (P Q : F[X]) (hQ : Q ≠ 0) (s : F[X] × F[X] × F[X])
    (hC : s.2.2 ≠ 0) (hratio : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2))
    (x : F[X]) (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true := by
  rw [verify_iff]
  refine ⟨hQ, hC, ?_⟩
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio + (Q * taylor 1 s.2.2) * hx

/-- Translate the forward multiplier equation to the paper's backward ratio.
The paper's multiplier is `g + 1`. -/
theorem forward_iff_backward (ρ : RatFunc F) :
    (∃ g : RatFunc F, ρ * Gosper.rationalShift 1 g - g = 1) ↔
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

theorem forward_iff_hypergeometric (ρ : RatFunc F) (hρ : ρ ≠ 0) :
    (∃ g : RatFunc F, ρ * Gosper.rationalShift 1 g - g = 1) ↔
      Gosper.HasHypergeometricAntidifference ρ :=
  (Gosper.hypergeometric_iff_forward ρ hρ).symm

variable {K : Type} [CommRing K] [IsDomain K] [DecidableEq K]
variable {L : Type} [CommRing L] [IsDomain L] [Algebra K L]
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
theorem gosperTerm_none_iff_degreeBound_neg
    (P Q : L[X]) :
    gosperTerm backend P Q = .ok none ↔
      ∃ A B : K[X],
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).1 = some A ∧
        descendPolynomial backend.descend (gosperNormal backend.normalization P Q).2.1 = some B ∧
        degreeBound backend.solver A (taylor (-1) B)
          (gosperNormal backend.normalization P Q).2.2 < 0 := by
  rw [gosperTerm_eq_ok_iff backend P Q none]
  apply exists_congr
  intro A
  apply exists_congr
  intro B
  rw [gosperSolve_none_iff_degreeBound_neg]


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

/-- A successful run supplies a ring normal form and a solver call over the input ring. -/
theorem gosperTerm_normalForm (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Option (Result L))
    (hrun : gosperTerm backend P Q = .ok result) :
    ∃ A B : K[X], ∃ C : L[X],
      gosperSolve backend.solver A (taylor (-1) B) C = result ∧
      normalFormValid (P.map (algebraMap L (FractionRing L)))
        (Q.map (algebraMap L (FractionRing L)))
        (A.map (algebraMap K (FractionRing L)),
          B.map (algebraMap K (FractionRing L)), C.map (algebraMap L (FractionRing L))) := by
  obtain ⟨A, B, hA, hB, hsolve⟩ := (gosperTerm_eq_ok_iff backend P Q result).mp hrun
  let normal := gosperNormal backend.normalization P Q
  have hmapA : A.map (algebraMap K L) = normal.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB : B.map (algebraMap K L) = normal.2.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  have hvalid := gosperNormal_spec backend.normalization hbackend.normalization
    P Q hP hQ normal rfl
  refine ⟨A, B, normal.2.2, hsolve, ?_⟩
  have hAF : A.map (algebraMap K (FractionRing L)) =
      normal.1.map (algebraMap L (FractionRing L)) := by
    simpa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L (FractionRing L)] using
      congrArg (Polynomial.map (algebraMap L (FractionRing L))) hmapA
  have hBF : B.map (algebraMap K (FractionRing L)) =
      normal.2.1.map (algebraMap L (FractionRing L)) := by
    simpa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L (FractionRing L)] using
      congrArg (Polynomial.map (algebraMap L (FractionRing L))) hmapB
  rw [hAF, hBF]
  exact hvalid

/-- A vanishing residual verifies the polynomial certificate over the input ring. -/
theorem gosperTerm_verified [DecidableEq L] (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    verify P Q c.numerator c.denominator = true := by
  classical
  have hKF : Function.Injective (algebraMap K (FractionRing L)) :=
    (IsFractionRing.injective L (FractionRing L)).comp hbackend.descend.injective
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_normalForm backend hbackend P Q hP hQ (some c) h
  let i : L →ₐ[K] FractionRing L := IsScalarTower.toAlgHom K L (FractionRing L)
  obtain ⟨δ, hδ, x, hnum, hden, hx⟩ := gosperSolve_sound backend.solver hbackend.solver
    A (taylor (-1) B) C i hKF c hsolve
    (by intro v hv; simp [hzero v hv])
  apply (verify_map_iff (algebraMap L (FractionRing L))
    (IsFractionRing.injective L (FractionRing L)) P Q c.numerator c.denominator).mp
  change verify (P.map i.toRingHom) (Q.map i.toRingHom)
    (c.numerator.map i.toRingHom) (c.denominator.map i.toRingHom) = true
  rw [hnum, hden]
  have hQF : Q.map i.toRingHom ≠ 0 :=
    (Polynomial.map_eq_zero_iff (IsFractionRing.injective L (FractionRing L))).not.mpr hQ
  have hδF : algebraMap K (FractionRing L) δ ≠ 0 :=
    fun hz => hδ (hKF (by simpa using hz))
  have hscaled := normalFormValid_scale_C _ _ _ _ _ _ hδF hvalid
  simpa [i] using normalForm_verify_solution_of_ratio _ _ hQF _
    hscaled.1.2.2 hscaled.2.2 x (by simpa [i] using hx)

/-- The returned multiplier satisfies its polynomial identity over the coefficient ring. -/
theorem gosperTerm_identity (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧ residual P Q c.numerator c.denominator = 0 := by
  classical
  exact verify_sound P Q _ _ (gosperTerm_verified backend hbackend P Q hP hQ c h hzero)

/-- Interpret the ring-valued output as a rational multiplier in its fraction field. -/
theorem gosperTerm_sound (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    let i := algebraMap L (FractionRing L)
    toRatFunc (P.map i) (Q.map i) * Gosper.rationalShift 1
      (toRatFunc (c.numerator.map i) (c.denominator.map i)) -
      toRatFunc (c.numerator.map i) (c.denominator.map i) = 1 := by
  classical
  exact verify_ratFunc _ _ _ _
    ((verify_map_iff (algebraMap L (FractionRing L)) (IsFractionRing.injective L (FractionRing L))
      P Q c.numerator c.denominator).mpr
        (gosperTerm_verified backend hbackend P Q hP hQ c h hzero))

/-- A returned multiplier with vanishing residual gives a hypergeometric antidifference. -/
theorem gosperTerm_hypergeometric (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) :
    Gosper.HasHypergeometricAntidifference
      (toRatFunc (P.map (algebraMap L (FractionRing L)))
        (Q.map (algebraMap L (FractionRing L)))) := by
  have hρ : toRatFunc (P.map (algebraMap L (FractionRing L)))
      (Q.map (algebraMap L (FractionRing L))) ≠ 0 := by
    have hi := IsFractionRing.injective L (FractionRing L)
    exact toRatFunc_ne_zero _ _ ((Polynomial.map_eq_zero_iff hi).not.mpr hP)
      ((Polynomial.map_eq_zero_iff hi).not.mpr hQ)
  exact (forward_iff_hypergeometric _ hρ).mp
    ⟨_, gosperTerm_sound backend hbackend P Q hP hQ c h hzero⟩

/-- The reconstructed forward antidifference advances by the input term. -/
theorem gosperTerm_step (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0) (a : ℕ → FractionRing L) (n : ℕ)
    (hQ : (Q.map (algebraMap L (FractionRing L))).eval (n : FractionRing L) ≠ 0)
    (hV : (c.denominator.map (algebraMap L (FractionRing L))).eval (n : FractionRing L) ≠ 0)
    (hVnext : (c.denominator.map (algebraMap L (FractionRing L))).eval ((n + 1 : ℕ) : FractionRing L) ≠ 0)
    (hratio : a (n + 1) * (Q.map (algebraMap L (FractionRing L))).eval (n : FractionRing L) = a n * (P.map (algebraMap L (FractionRing L))).eval (n : FractionRing L)) :
    a (n + 1) * ((c.numerator.map (algebraMap L (FractionRing L))).eval ((n + 1 : ℕ) : FractionRing L) /
        (c.denominator.map (algebraMap L (FractionRing L))).eval ((n + 1 : ℕ) : FractionRing L)) -
      a n * ((c.numerator.map (algebraMap L (FractionRing L))).eval (n : FractionRing L) / (c.denominator.map (algebraMap L (FractionRing L))).eval (n : FractionRing L)) = a n := by
  classical
  have hv := (verify_map_iff (algebraMap L (FractionRing L))
    (IsFractionRing.injective L (FractionRing L)) P Q c.numerator c.denominator).mpr
    (gosperTerm_verified backend hbackend P Q hP0 hQ0 c h hzero)
  have he := verify_at _ _ _ _ hv
    (n : FractionRing L) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * he

/-- The returned multiplier telescopes a finite sum under the stated denominator conditions. -/
theorem gosperTerm_sum (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok (some c))
    (hzero : ∀ value ∈ c.residual, value = 0)
    (a : ℕ → FractionRing L) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, (Q.map (algebraMap L (FractionRing L))).eval (k : FractionRing L) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, (c.denominator.map (algebraMap L (FractionRing L))).eval (k : FractionRing L) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * (Q.map (algebraMap L (FractionRing L))).eval (k : FractionRing L) = a k * (P.map (algebraMap L (FractionRing L))).eval (k : FractionRing L)) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * ((c.numerator.map (algebraMap L (FractionRing L))).eval (n : FractionRing L) / (c.denominator.map (algebraMap L (FractionRing L))).eval (n : FractionRing L)) -
        a m * ((c.numerator.map (algebraMap L (FractionRing L))).eval (m : FractionRing L) / (c.denominator.map (algebraMap L (FractionRing L))).eval (m : FractionRing L)) := by
  calc
    _ = ∑ k ∈ Finset.Ico m n,
        (a (k + 1) * ((c.numerator.map (algebraMap L (FractionRing L))).eval ((k + 1 : ℕ) : FractionRing L) /
            (c.denominator.map (algebraMap L (FractionRing L))).eval ((k + 1 : ℕ) : FractionRing L)) -
          a k * ((c.numerator.map (algebraMap L (FractionRing L))).eval (k : FractionRing L) / (c.denominator.map (algebraMap L (FractionRing L))).eval (k : FractionRing L))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact (gosperTerm_step backend hbackend
        P Q hP0 hQ0 c h hzero a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub
      (fun k => a k * ((c.numerator.map (algebraMap L (FractionRing L))).eval (k : FractionRing L) / (c.denominator.map (algebraMap L (FractionRing L))).eval (k : FractionRing L))) hmn

end Gosper.Algorithm
