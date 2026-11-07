module

public import SympyProofs.Sum.Gosper.Algorithm.Descent
public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationSpecialization
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationCorrectness
public import SympyProofs.Sum.Gosper.Rational
public import SympyProofs.Sum.Gosper.Hypergeometric

/-! Soundness and finite-sum identities with or without a remainder,
and the meaning of coefficient descent errors. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {E : Type*} [Field E]

theorem verify_identity [DecidableEq E] (P Q U V : E[X]) (h : verify P Q U V = true) (x : E) :
    P.eval x * U.eval (x + 1) * V.eval x -
        Q.eval x * U.eval x * V.eval (x + 1) =
      Q.eval x * V.eval x * V.eval (x + 1) := by
  have he := congrArg (fun p : E[X] => p.eval x) (verify_sound P Q U V h).2.2
  simpa only [residual, Polynomial.eval_sub, Polynomial.eval_mul, taylor_eval,
    Polynomial.eval_zero, sub_eq_zero] using he

theorem verify_at [DecidableEq E] (P Q U V : E[X]) (h : verify P Q U V = true) (x : E)
    (hQ : Q.eval x ≠ 0) (hV : V.eval x ≠ 0) (hVnext : V.eval (x + 1) ≠ 0) :
    P.eval x / Q.eval x * (U.eval (x + 1) / V.eval (x + 1)) -
      U.eval x / V.eval x = 1 := by
  have hi := verify_identity P Q U V h x
  field_simp
  linear_combination hi

def toRatFunc {R : Type*} [CommRing R] [IsDomain R] (U V : R[X]) : RatFunc R :=
  algebraMap R[X] (RatFunc R) U / algebraMap R[X] (RatFunc R) V

theorem toRatFunc_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (U V : R[X]) (hU : U ≠ 0) (hV : V ≠ 0) :
    toRatFunc U V ≠ 0 := by
  unfold toRatFunc
  exact div_ne_zero (by simpa using hU) (by simpa using hV)

theorem verify_ratFunc {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (P Q U V : R[X]) (h : verify P Q U V = true) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc U V) - toRatFunc U V = 1 := by
  obtain ⟨hQ, hV, he⟩ := verify_sound P Q U V h
  let ι := algebraMap R[X] (RatFunc R)
  have map_ne (p : R[X]) (hp : p ≠ 0) : ι p ≠ 0 := by
    intro hz
    exact hp ((IsFractionRing.injective R[X] (RatFunc R)) (by simpa [ι] using hz))
  have hq := map_ne _ hQ
  have hv := map_ne _ hV
  have hsv := map_ne _ ((taylor_eq_zero 1 V).not.mpr hV)
  have hm := congrArg ι he
  simp only [residual, map_sub, map_mul, map_zero] at hm
  simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial]
  change ι P / ι Q * (ι (taylor 1 U) / ι (taylor 1 V)) - ι U / ι V = 1
  field_simp
  linear_combination hm

/-- A normalized ratio gives a reduction identity even when its polynomial
equation has a nonzero remainder. -/
theorem normalForm_reduction_identity {R : Type*} [CommRing R]
    (P Q A B V x : R[X])
    (hratio : P * (B * V) = Q * (A * taylor 1 V)) :
    residual P Q (taylor (-1) B * x) V =
      -(Q * taylor 1 V * (V - (A * taylor 1 x - taylor (-1) B * x))) := by
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio

/-- The cross-multiplied reduction identity gives a rational decomposition. -/
theorem reduction_ratFunc {R : Type*} [CommRing R] [IsDomain R]
    (P Q U V W : R[X]) (hQ : Q ≠ 0) (hV : V ≠ 0)
    (h : residual P Q U V = -(Q * taylor 1 V * W)) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc U V) - toRatFunc U V +
      toRatFunc W V = 1 := by
  let ι := algebraMap R[X] (RatFunc R)
  have map_ne (p : R[X]) (hp : p ≠ 0) : ι p ≠ 0 := by
    intro hz
    exact hp ((IsFractionRing.injective R[X] (RatFunc R)) (by simpa [ι] using hz))
  have hq := map_ne _ hQ
  have hv := map_ne _ hV
  have hsv := map_ne _ ((taylor_eq_zero 1 V).not.mpr hV)
  have hm := congrArg ι h
  simp only [residual, map_sub, map_mul, map_neg] at hm
  simp only [toRatFunc, map_div₀, Gosper.rationalShift_polynomial]
  change ι P / ι Q * (ι (taylor 1 U) / ι (taylor 1 V)) - ι U / ι V +
    ι W / ι V = 1
  field_simp
  linear_combination hm

/-- Evaluate a polynomial reduction identity wherever its denominators do not vanish. -/
theorem reduction_at (P Q U V W : E[X])
    (h : residual P Q U V = -(Q * taylor 1 V * W)) (x : E)
    (hQ : Q.eval x ≠ 0) (hV : V.eval x ≠ 0) (hVnext : V.eval (x + 1) ≠ 0) :
    P.eval x / Q.eval x * (U.eval (x + 1) / V.eval (x + 1)) -
      U.eval x / V.eval x + W.eval x / V.eval x = 1 := by
  have he := congrArg (fun p : E[X] => p.eval x) h
  simp only [residual, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
    taylor_eval] at he
  field_simp
  linear_combination he

/-- A reduction separates one input term into a forward difference and its residual. -/
theorem reduction_step (P Q U V W : E[X])
    (h : residual P Q U V = -(Q * taylor 1 V * W)) (a : ℕ → E) (n : ℕ)
    (hQ : Q.eval (n : E) ≠ 0) (hV : V.eval (n : E) ≠ 0)
    (hVnext : V.eval ((n + 1 : ℕ) : E) ≠ 0)
    (hratio : a (n + 1) * Q.eval (n : E) = a n * P.eval (n : E)) :
    a n = a (n + 1) * (U.eval ((n + 1 : ℕ) : E) / V.eval ((n + 1 : ℕ) : E)) -
      a n * (U.eval (n : E) / V.eval (n : E)) +
      a n * (W.eval (n : E) / V.eval (n : E)) := by
  have hi := reduction_at P Q U V W h (n : E) hQ hV (by simpa using hVnext)
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination -a n * hi

/-- A polynomial reduction reconstructs a finite sum from its endpoints and residual sum. -/
theorem reduction_sum (P Q U V W : E[X])
    (h : residual P Q U V = -(Q * taylor 1 V * W))
    (a : ℕ → E) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, Q.eval (k : E) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, V.eval (k : E) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * Q.eval (k : E) = a k * P.eval (k : E)) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * (U.eval (n : E) / V.eval (n : E)) -
        a m * (U.eval (m : E) / V.eval (m : E)) +
        ∑ k ∈ Finset.Ico m n, a k * (W.eval (k : E) / V.eval (k : E)) := by
  calc
    _ = ∑ k ∈ Finset.Ico m n,
        ((a (k + 1) * (U.eval ((k + 1 : ℕ) : E) / V.eval ((k + 1 : ℕ) : E)) -
          a k * (U.eval (k : E) / V.eval (k : E))) +
          a k * (W.eval (k : E) / V.eval (k : E))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact reduction_step P Q U V W h a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_Ico_sub
        (fun k => a k * (U.eval (k : E) / V.eval (k : E))) hmn]

/-- The normalized equation and ratio identity imply the certificate identity;
shift-coprimality is not needed for this direction. -/
theorem normalForm_verify_solution_of_ratio [DecidableEq E]
    (P Q : E[X]) (hQ : Q ≠ 0) (s : E[X] × E[X] × E[X])
    (hC : s.2.2 ≠ 0) (hratio : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2))
    (x : E[X]) (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true := by
  rw [verify_iff]
  refine ⟨hQ, hC, ?_⟩
  simp only [residual, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  linear_combination taylor 1 x * hratio + (Q * taylor 1 s.2.2) * hx

theorem normalForm_verify_solution [DecidableEq E]
    (P Q : E[X]) (hQ : Q ≠ 0) (s : E[X] × E[X] × E[X])
    (hs : normalFormValid P Q s) (x : E[X])
    (hx : s.1 * taylor 1 x - taylor (-1) s.2.1 * x = s.2.2) :
    verify P Q (taylor (-1) s.2.1 * x) s.2.2 = true :=
  normalForm_verify_solution_of_ratio P Q hQ s hs.1.2.2 hs.2.2 x hx

/-- Translate the forward multiplier equation to the paper's backward ratio.
The paper's multiplier is `g + 1`. -/
theorem forward_iff_backward (ρ : RatFunc E) :
    (∃ g : RatFunc E, ρ * Gosper.rationalShift 1 g - g = 1) ↔
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

theorem forward_iff_hypergeometric {R : Type*} [CommRing R] [IsDomain R]
    (ρ : RatFunc R) (hρ : ρ ≠ 0) :
    (∃ g : RatFunc R, ρ * Gosper.rationalShift 1 g - g = 1) ↔
      Gosper.HasHypergeometricAntidifference ρ :=
  (Gosper.hypergeometric_iff_forward ρ hρ).symm

variable {K : Type} [CommRing K] [IsDomain K] [DecidableEq K] [Div K]
variable {L : Type} [CommRing L] [IsDomain L] [Algebra K L] [Div L]
variable (backend : TermBackend K L)

private theorem gosperTerm_eq (P Q : L[X]) :
    gosperTerm backend P Q =
      match descendPolynomial backend.descend (gosperNormal backend P Q).1 with
      | none => .error .A
      | some A => match descendPolynomial backend.descend (gosperNormal backend P Q).2.1 with
        | none => .error .B
        | some B => .ok (gosperSolve backend A (taylor (-1) B) (gosperNormal backend P Q).2.2) := by
  cases hA : descendPolynomial backend.descend (gosperNormal backend P Q).1 with
  | none => simp only [gosperTerm, hA]; rfl
  | some A =>
    cases hB : descendPolynomial backend.descend (gosperNormal backend P Q).2.1 with
    | none => simp only [gosperTerm, hA, hB]; rfl
    | some B => simp only [gosperTerm, hA, hB]; rfl

/-- Successful descent leaves exactly the normalized solver call over `K`. -/
theorem gosperTerm_eq_of_descent (P Q : L[X]) (A B : K[X])
    (hA : descendPolynomial backend.descend (gosperNormal backend P Q).1 = some A)
    (hB : descendPolynomial backend.descend (gosperNormal backend P Q).2.1 = some B) :
    gosperTerm backend P Q =
      .ok (gosperSolve backend A (taylor (-1) B) (gosperNormal backend P Q).2.2) := by
  simp [gosperTerm_eq, hA, hB]

/-- An `ok` result records successful descent of both normalized polynomials. -/
theorem gosperTerm_eq_ok_iff (P Q : L[X]) (c : Result L) :
    gosperTerm backend P Q = .ok c ↔
      ∃ A B : K[X],
        descendPolynomial backend.descend (gosperNormal backend P Q).1 = some A ∧
        descendPolynomial backend.descend (gosperNormal backend P Q).2.1 = some B ∧
        gosperSolve backend A (taylor (-1) B) (gosperNormal backend P Q).2.2 = c := by
  cases hA : descendPolynomial backend.descend (gosperNormal backend P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- The first descent error means that the normalized `A` is not defined over `K`. -/
theorem gosperTerm_error_A_iff (hdesc : ∀ c a, backend.descend c = some a ↔ algebraMap K L a = c)
    (P Q : L[X]) :
    gosperTerm backend P Q = .error .A ↔
      ¬∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend P Q).1 := by
  rw [← descendPolynomial_eq_none_iff backend.descend hdesc]
  cases hA : descendPolynomial backend.descend (gosperNormal backend P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A `B` descent error occurs only after `A` has descended successfully. -/
theorem gosperTerm_error_B_iff (hdesc : ∀ c a, backend.descend c = some a ↔ algebraMap K L a = c)
    (P Q : L[X]) :
    gosperTerm backend P Q = .error .B ↔
      (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend P Q).1) ∧
      ¬∃ B : K[X], B.map (algebraMap K L) = (gosperNormal backend P Q).2.1 := by
  have hA : (∃ A : K[X], A.map (algebraMap K L) = (gosperNormal backend P Q).1) ↔
      ∃ A, descendPolynomial backend.descend (gosperNormal backend P Q).1 = some A := by
    simp only [descendPolynomial_eq_some_iff backend.descend hdesc]
  rw [hA, ← descendPolynomial_eq_none_iff backend.descend hdesc]
  cases hA : descendPolynomial backend.descend (gosperNormal backend P Q).1 <;>
    cases hB : descendPolynomial backend.descend (gosperNormal backend P Q).2.1 <;>
    simp [gosperTerm_eq, hA, hB]

/-- A successful run supplies a ring normal form and a solver call over the input ring. -/
theorem gosperTerm_normalForm (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (result : Result L)
    (hrun : gosperTerm backend P Q = .ok result) :
    ∃ A B : K[X], ∃ C : L[X],
      gosperSolve backend A (taylor (-1) B) C = result ∧
      normalFormValid (P.map (algebraMap L (FractionRing L)))
        (Q.map (algebraMap L (FractionRing L)))
        (A.map (algebraMap K (FractionRing L)),
          B.map (algebraMap K (FractionRing L)), C.map (algebraMap L (FractionRing L))) := by
  obtain ⟨A, B, hA, hB, hsolve⟩ := (gosperTerm_eq_ok_iff backend P Q result).mp hrun
  let normal := gosperNormal backend P Q
  have hmapA : A.map (algebraMap K L) = normal.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB : B.map (algebraMap K L) = normal.2.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  have hvalid := gosperNormal_spec backend hbackend
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

/-- Every returned result satisfies the exact polynomial reduction identity,
including results with a nonzero residual. -/
theorem gosperTerm_reduction_identity (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r) :
    Q ≠ 0 ∧ r.denominator ≠ 0 ∧
      residual P Q r.numerator r.denominator =
        -(Q * taylor 1 r.denominator * r.residual) := by
  obtain ⟨A, B, hA, hB, hsolve⟩ :=
    (gosperTerm_eq_ok_iff backend P Q r).mp hrun
  let normal := gosperNormal backend P Q
  have hmapA : A.map (algebraMap K L) = normal.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB : B.map (algebraMap K L) = normal.2.1 :=
    (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  obtain ⟨hn, hratio⟩ := gosperNormal_sound backend hbackend
    P Q hP hQ normal rfl
  obtain ⟨δ, hδ, x, hu, hv, he⟩ := gosperSolve_reduction_data backend hbackend
    A (taylor (-1) B) normal.2.2 r hsolve
  have hδL : algebraMap K L δ ≠ 0 :=
    fun hz => hδ (hbackend.algebraMap_injective (by simpa using hz))
  have hv0 : r.denominator ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hδL) hn.2.2
  have hu' : r.numerator = taylor (-1) normal.2.1 * x := by
    simpa only [Polynomial.map_taylor, map_neg, map_one, hmapB] using hu
  have he' : r.residual = r.denominator -
      (normal.1 * taylor 1 x - taylor (-1) normal.2.1 * x) := by
    simpa only [Polynomial.map_taylor, map_neg, map_one, hmapA, hmapB] using he
  have hratioV : P * (normal.2.1 * r.denominator) =
      Q * (normal.1 * taylor 1 r.denominator) := by
    rw [hv]
    simp only [taylor_mul, taylor_C]
    linear_combination Polynomial.C (algebraMap K L δ) * hratio
  refine ⟨hQ, hv0, ?_⟩
  rw [hu', he']
  exact normalForm_reduction_identity P Q normal.1 normal.2.1 r.denominator x hratioV

/-- The input multiplier is the forward difference multiplier plus the returned
residual multiplier; no vanishing condition is required. -/
theorem gosperTerm_reduction (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc r.numerator r.denominator) -
      toRatFunc r.numerator r.denominator + toRatFunc r.residual r.denominator = 1 := by
  obtain ⟨hq, hv, he⟩ := gosperTerm_reduction_identity backend hbackend P Q hP hQ r hrun
  exact reduction_ratFunc P Q r.numerator r.denominator r.residual hq hv he

/-- A vanishing residual verifies the polynomial certificate over the input ring. -/
theorem gosperTerm_verified [DecidableEq L] (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0) :
    verify P Q c.numerator c.denominator = true := by
  classical
  have hKF : Function.Injective (algebraMap K (FractionRing L)) :=
    (IsFractionRing.injective L (FractionRing L)).comp hbackend.algebraMap_injective
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_normalForm backend hbackend P Q hP hQ c h
  let i : L →ₐ[K] FractionRing L := IsScalarTower.toAlgHom K L (FractionRing L)
  obtain ⟨δ, hδ, x, hnum, hden, hx⟩ := gosperSolve_sound backend hbackend
    A (taylor (-1) B) C i hKF c hsolve
    (by simp [hzero])
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
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0) :
    Q ≠ 0 ∧ c.denominator ≠ 0 ∧ residual P Q c.numerator c.denominator = 0 := by
  classical
  exact verify_sound P Q _ _ (gosperTerm_verified backend hbackend P Q hP hQ c h hzero)

/-- The returned multiplier satisfies the rational-function identity over the input domain. -/
theorem gosperTerm_sound (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0) :
    toRatFunc P Q * Gosper.rationalShift 1 (toRatFunc c.numerator c.denominator) -
      toRatFunc c.numerator c.denominator = 1 := by
  classical
  exact verify_ratFunc _ _ _ _
    (gosperTerm_verified backend hbackend P Q hP hQ c h hzero)

/-- A returned multiplier with a vanishing residual gives a hypergeometric antidifference. -/
theorem gosperTerm_hypergeometric (hbackend : backend.Valid)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0) :
    Gosper.HasHypergeometricAntidifference (toRatFunc P Q) := by
  exact (forward_iff_hypergeometric _ (toRatFunc_ne_zero P Q hP hQ)).mp
    ⟨_, gosperTerm_sound backend hbackend P Q hP hQ c h hzero⟩

variable [Algebra L E]

/-- The reconstructed forward antidifference advances by the input term. -/
theorem gosperTerm_step (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0) (a : ℕ → E) (n : ℕ)
    (hQ : aeval (n : E) Q ≠ 0)
    (hV : aeval (n : E) c.denominator ≠ 0)
    (hVnext : aeval ((n + 1 : ℕ) : E) c.denominator ≠ 0)
    (hratio : a (n + 1) * aeval (n : E) Q = a n * aeval (n : E) P) :
    a (n + 1) * (aeval ((n + 1 : ℕ) : E) c.numerator /
        aeval ((n + 1 : ℕ) : E) c.denominator) -
      a n * (aeval (n : E) c.numerator / aeval (n : E) c.denominator) = a n := by
  have ht (p : L[X]) : aeval (n : E) (taylor 1 p) = aeval ((n : E) + 1) p := by
    simp only [← eval_map_algebraMap, map_taylor, map_one, taylor_eval]
  have he := congrArg (aeval (n : E))
    (gosperTerm_identity backend hbackend P Q hP0 hQ0 c h hzero).2.2
  simp only [residual, map_sub, map_mul, map_zero, ht] at he
  have hvnext : aeval ((n : E) + 1) c.denominator ≠ 0 := by simpa using hVnext
  have hi : aeval (n : E) P / aeval (n : E) Q *
        (aeval ((n : E) + 1) c.numerator / aeval ((n : E) + 1) c.denominator) -
      aeval (n : E) c.numerator / aeval (n : E) c.denominator = 1 := by
    field_simp
    linear_combination he
  have ha := (eq_div_iff hQ).mpr hratio
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ha]
  linear_combination a n * hi

/-- The returned multiplier telescopes a finite sum in any target field where
its evaluated denominators do not vanish. -/
theorem gosperTerm_sum (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (c : Result L)
    (h : gosperTerm backend P Q = .ok c)
    (hzero : c.residual = 0)
    (a : ℕ → E) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, aeval (k : E) Q ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, aeval (k : E) c.denominator ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * aeval (k : E) Q = a k * aeval (k : E) P) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * (aeval (n : E) c.numerator / aeval (n : E) c.denominator) -
        a m * (aeval (m : E) c.numerator / aeval (m : E) c.denominator) := by
  calc
    _ = ∑ k ∈ Finset.Ico m n,
        (a (k + 1) * (aeval ((k + 1 : ℕ) : E) c.numerator /
            aeval ((k + 1 : ℕ) : E) c.denominator) -
          a k * (aeval (k : E) c.numerator / aeval (k : E) c.denominator)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact (gosperTerm_step backend hbackend
        P Q hP0 hQ0 c h hzero a k (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (hratio k hk)).symm
    _ = _ := Finset.sum_Ico_sub
      (fun k => a k * (aeval (k : E) c.numerator / aeval (k : E) c.denominator)) hmn

/-- The residual summand of a returned result is the input term times
`residual / denominator`, with evaluation in the target field. -/
theorem gosperTerm_reduction_step (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r) (a : ℕ → E) (n : ℕ)
    (hQ : aeval (n : E) Q ≠ 0) (hV : aeval (n : E) r.denominator ≠ 0)
    (hVnext : aeval ((n + 1 : ℕ) : E) r.denominator ≠ 0)
    (hratio : a (n + 1) * aeval (n : E) Q = a n * aeval (n : E) P) :
    a n = a (n + 1) * (aeval ((n + 1 : ℕ) : E) r.numerator /
        aeval ((n + 1 : ℕ) : E) r.denominator) -
      a n * (aeval (n : E) r.numerator / aeval (n : E) r.denominator) +
      a n * (aeval (n : E) r.residual / aeval (n : E) r.denominator) := by
  have he := congrArg (Polynomial.map (algebraMap L E))
    (gosperTerm_reduction_identity backend hbackend P Q hP0 hQ0 r hrun).2.2
  simp only [residual_map, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_taylor, map_one] at he
  simpa only [eval_map_algebraMap] using
    reduction_step _ _ _ _ _ he a n
      (by simpa only [eval_map_algebraMap] using hQ)
      (by simpa only [eval_map_algebraMap] using hV)
      (by simpa only [eval_map_algebraMap] using hVnext)
      (by simpa only [eval_map_algebraMap] using hratio)

/-- A returned result reconstructs a finite sum as its endpoint contribution
plus the sum of its remaining terms. -/
theorem gosperTerm_reduction_sum (hbackend : backend.Valid)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (a : ℕ → E) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, aeval (k : E) Q ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, aeval (k : E) r.denominator ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * aeval (k : E) Q = a k * aeval (k : E) P) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * (aeval (n : E) r.numerator / aeval (n : E) r.denominator) -
        a m * (aeval (m : E) r.numerator / aeval (m : E) r.denominator) +
        ∑ k ∈ Finset.Ico m n, a k * (aeval (k : E) r.residual / aeval (k : E) r.denominator) := by
  have he := congrArg (Polynomial.map (algebraMap L E))
    (gosperTerm_reduction_identity backend hbackend P Q hP0 hQ0 r hrun).2.2
  simp only [residual_map, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_taylor, map_one] at he
  simpa only [eval_map_algebraMap] using
    reduction_sum _ _ _ _ _ he a m n hmn
      (by simpa only [eval_map_algebraMap] using hQ)
      (by simpa only [eval_map_algebraMap] using hV)
      (by simpa only [eval_map_algebraMap] using hratio)

end Gosper.Algorithm
