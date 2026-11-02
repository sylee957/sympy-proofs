module

public import SympyProofs.Sum.Gosper.Algorithm.SolverSpecialization
public import SympyProofs.Sum.Gosper.Algorithm.Completeness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationSpecialization

/-! Specialize a retained `gosperTerm` output through a coefficient ring.
The embedding records the computation field; evaluation may lower degrees or
annihilate residuals. The specialized input and certificate denominators must
remain nonzero. No normalization or coefficient descent is rerun. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [DecidableEq K]
  [DecidablePred (IsInteger ℤ : K → Prop)]
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
  [DecidablePred (IsInteger ℤ : L → Prop)] [Algebra K L]
variable {R : Type} [CommRing R] [Algebra K R]
variable {E : Type} [Field E] [Algebra K E]
variable (backend : TermBackend K L)

/-- Recover the fixed-field solver and its specialized normal form from the full run. -/
private theorem gosperTerm_specialize_data (hbackend : backend.Valid)
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (P Q : R[X]) (r : Result R)
    (hrun : gosperTerm backend (P.map i.toRingHom) (Q.map i.toRingHom) =
      .ok (some (r.map i.toRingHom)))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    ∃ A B : K[X],
      gosperSolve backend.solver A (taylor (-1) B) r.denominator = some r ∧
      normalFormValid (P.map f.toRingHom) (Q.map f.toRingHom)
        (A.map (algebraMap K E), B.map (algebraMap K E), r.denominator.map f.toRingHom) := by
  have hP0 : P ≠ 0 := fun hz => hP (by simp [hz])
  have hQ0 : Q ≠ 0 := fun hz => hQ (by simp [hz])
  have hPL : P.map i.toRingHom ≠ 0 := (Polynomial.map_eq_zero_iff hi).not.mpr hP0
  have hQL : Q.map i.toRingHom ≠ 0 := (Polynomial.map_eq_zero_iff hi).not.mpr hQ0
  obtain ⟨A, B, hA, hB, hsolve⟩ :=
    (gosperTerm_eq_ok_iff backend _ _ _).mp hrun
  have hmapA := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ A).mp hA
  have hmapB := (descendPolynomial_eq_some_iff backend.descend hbackend.descend _ B).mp hB
  have hden := gosperSolve_denominator backend.solver hbackend.solver A (taylor (-1) B)
    _ _ hsolve
  change r.denominator.map i.toRingHom = _ at hden
  have hsolveR : gosperSolve backend.solver A (taylor (-1) B) r.denominator = some r := by
    apply gosperSolve_of_map backend.solver hbackend.solver A (taylor (-1) B)
      r.denominator i hi r
    rwa [hden]
  have hvalid : normalFormValid (P.map i.toRingHom) (Q.map i.toRingHom)
      (A.map (algebraMap K L), B.map (algebraMap K L), r.denominator.map i.toRingHom) := by
    rw [hmapA, hmapB, hden]
    exact gosperNormal_spec backend.normalization hbackend.normalization _ _ hPL hQL _ rfl
  refine ⟨A, B, hsolveR, ?_⟩
  exact normalFormValid_specialize i hi f A B r.denominator P Q hvalid hV

/-- Evaluating the retained conditions verifies the specialized input, even when
the generic residual is nonzero or evaluation lowers the numerator degree. -/
theorem gosperTerm_specialize_verified [DecidableEq E] (hbackend : backend.Valid)
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (P Q : R[X]) (r : Result R)
    (hrun : gosperTerm backend (P.map i.toRingHom) (Q.map i.toRingHom) =
      .ok (some (r.map i.toRingHom)))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    verify (P.map f.toRingHom) (Q.map f.toRingHom)
      (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = true := by
  obtain ⟨A, B, hsolve, hvalid⟩ :=
    gosperTerm_specialize_data backend hbackend i hi f P Q r hrun hP hQ hV
  obtain ⟨x, hu, _, hx⟩ := gosperSolve_specialize_sound backend.solver hbackend.solver
    A (taylor (-1) B) r.denominator f r hsolve hzero
  simp only [Polynomial.map_taylor, map_neg, map_one] at hu hx
  rw [hu]
  exact normalForm_verify_solution _ _ hQ _ hvalid x hx

/-- The specialized candidate is a multiplier for the original specialized ratio. -/
theorem gosperTerm_specialize_sound (hbackend : backend.Valid)
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (P Q : R[X]) (r : Result R)
    (hrun : gosperTerm backend (P.map i.toRingHom) (Q.map i.toRingHom) =
      .ok (some (r.map i.toRingHom)))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom) *
        Gosper.rationalShift 1
          (toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom)) -
      toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = 1 := by
  classical
  exact verify_ratFunc _ _ _ _
    (gosperTerm_specialize_verified backend hbackend i hi f P Q r hrun hP hQ hV hzero)

/-- The evaluated residual characterizes summability of the specialized input.
The successful run supplies coefficient descent; callers need no normal-form hypotheses. -/
theorem gosperTerm_specialize_complete [CharZero K] [CharZero E]
    (hbackend : backend.Valid)
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (P Q : R[X]) (r : Result R)
    (hrun : gosperTerm backend (P.map i.toRingHom) (Q.map i.toRingHom) =
      .ok (some (r.map i.toRingHom)))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    (∀ value ∈ r.residual, f value = 0) ↔
      Gosper.HasHypergeometricAntidifference
        (toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom)) := by
  obtain ⟨A, B, hsolve, hvalid⟩ :=
    gosperTerm_specialize_data backend hbackend i hi f P Q r hrun hP hQ hV
  have hA : A ≠ 0 := by simpa using hvalid.1.1
  have hB : taylor (-1 : K) B ≠ 0 := by simpa using hvalid.1.2.1
  rw [gosperSolve_specialize_complete backend.solver hbackend.solver
    A (taylor (-1) B) r.denominator f r hsolve hA hB]
  simpa using (normalForm_hypergeometric_iff_polynomial
    (P.map f.toRingHom) (Q.map f.toRingHom) hP hQ _ hvalid).symm

/-- Interpret a specialized output as the two endpoints of a finite sum. -/
theorem gosperTerm_specialize_sum (hbackend : backend.Valid)
    (i : R →ₐ[K] L) (hi : Function.Injective i) (f : R →ₐ[K] E)
    (P Q : R[X]) (r : Result R)
    (hrun : gosperTerm backend (P.map i.toRingHom) (Q.map i.toRingHom) =
      .ok (some (r.map i.toRingHom)))
    (hP0 : P.map f.toRingHom ≠ 0) (hQ0 : Q.map f.toRingHom ≠ 0)
    (hV0 : r.denominator.map f.toRingHom ≠ 0)
    (hzero : ∀ value ∈ r.residual, f value = 0)
    (a : ℕ → E) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, (Q.map f.toRingHom).eval (k : E) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, (r.denominator.map f.toRingHom).eval (k : E) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * (Q.map f.toRingHom).eval (k : E) =
        a k * (P.map f.toRingHom).eval (k : E)) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * ((r.numerator.map f.toRingHom).eval (n : E) /
          (r.denominator.map f.toRingHom).eval (n : E)) -
        a m * ((r.numerator.map f.toRingHom).eval (m : E) /
          (r.denominator.map f.toRingHom).eval (m : E)) := by
  classical
  have hv := gosperTerm_specialize_verified backend hbackend i hi f P Q r hrun
    hP0 hQ0 hV0 hzero
  calc
    _ = ∑ k ∈ Finset.Ico m n,
        (a (k + 1) * ((r.numerator.map f.toRingHom).eval ((k + 1 : ℕ) : E) /
            (r.denominator.map f.toRingHom).eval ((k + 1 : ℕ) : E)) -
          a k * ((r.numerator.map f.toRingHom).eval (k : E) /
            (r.denominator.map f.toRingHom).eval (k : E))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have he := verify_at _ _ _ _ hv (k : E) (hQ k hk)
        (hV k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩))
        (by simpa using hV (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      have ha := (eq_div_iff (hQ k hk)).mpr (hratio k hk)
      symm
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ha]
      linear_combination a k * he
    _ = _ := Finset.sum_Ico_sub
      (fun k => a k * ((r.numerator.map f.toRingHom).eval (k : E) /
        (r.denominator.map f.toRingHom).eval (k : E))) hmn

end Gosper.Algorithm
