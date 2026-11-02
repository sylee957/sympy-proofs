module

public import SympyProofs.Sum.Gosper.Algorithm.SolverCorrectness
public import SympyProofs.Sum.Gosper.Algorithm.Completeness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationSpecialization

/-! Specialize a retained `gosperTerm` output by evaluating its coefficient ring.
Evaluation embeds the constant domain, but may lower degrees or annihilate parameter
residuals. The input and certificate denominators must remain nonzero. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {K : Type} [CommRing K] [IsDomain K] [DecidableEq K]
variable {L : Type} [CommRing L] [IsDomain L] [Algebra K L]
variable {E : Type} [Field E] [Algebra K E]
variable (backend : TermBackend K L)

/-- Recover the constant-domain solver and its specialized normal form from the full run. -/
private theorem gosperTerm_specialize_data (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok (some r))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    ∃ A B : K[X], ∃ C : L[X],
      gosperSolve backend.solver A (taylor (-1) B) C = some r ∧
      normalFormValid (P.map f.toRingHom) (Q.map f.toRingHom)
        (A.map (algebraMap K E), B.map (algebraMap K E), C.map f.toRingHom) := by
  have hP0 : P ≠ 0 := fun hz => hP (by simp [hz])
  have hQ0 : Q ≠ 0 := fun hz => hQ (by simp [hz])
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_normalForm backend hbackend P Q hP0 hQ0 (some r) hrun
  obtain ⟨δ, _, hden⟩ := gosperSolve_denominator backend.solver hbackend.solver
    A (taylor (-1) B) C r hsolve
  have hC : C.map f.toRingHom ≠ 0 := by
    intro hzero
    apply hV
    rw [hden]
    rw [Polynomial.map_mul, hzero, mul_zero]
  refine ⟨A, B, C, hsolve, ?_⟩
  have hKi : Function.Injective (algebraMap K (FractionRing L)) := by
    rw [IsScalarTower.algebraMap_eq K L (FractionRing L)]
    exact (IsFractionRing.injective L (FractionRing L)).comp hbackend.descend.injective
  exact normalFormValid_specialize (IsScalarTower.toAlgHom K L (FractionRing L))
    (IsFractionRing.injective L (FractionRing L)) f hKi hK
    A B C P Q hvalid hC

/-- Evaluating the retained conditions verifies the specialized input, even when
the generic residual is nonzero or evaluation lowers the numerator degree. -/
theorem gosperTerm_specialize_verified [DecidableEq E] (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok (some r))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    verify (P.map f.toRingHom) (Q.map f.toRingHom)
      (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = true := by
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_specialize_data backend hbackend f hK P Q r hrun hP hQ hV
  obtain ⟨δ, hδ, x, hu, hd, hx⟩ := gosperSolve_specialize_sound backend.solver hbackend.solver
    A (taylor (-1) B) C f hK r hsolve hzero
  simp only [Polynomial.map_taylor, map_neg, map_one] at hu hx
  have hδE : algebraMap K E δ ≠ 0 := fun hz => hδ (hK (by simpa using hz))
  have hscaled := normalFormValid_scale_C _ _ _ _ _ (algebraMap K E δ) hδE hvalid
  rw [hu, hd]
  exact normalForm_verify_solution _ _ hQ _ hscaled x hx

/-- The specialized candidate is a multiplier for the original specialized ratio. -/
theorem gosperTerm_specialize_sound (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok (some r))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : ∀ value ∈ r.residual, f value = 0) :
    toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom) *
        Gosper.rationalShift 1
          (toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom)) -
      toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = 1 := by
  classical
  exact verify_ratFunc _ _ _ _
    (gosperTerm_specialize_verified backend hbackend f hK P Q r hrun hP hQ hV hzero)

/-- The evaluated residual characterizes summability of the specialized input.
The successful run supplies coefficient descent; callers need no normal-form hypotheses. -/
theorem gosperTerm_specialize_complete [CharZero K] [CharZero E]
    (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok (some r))
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    (∀ value ∈ r.residual, f value = 0) ↔
      Gosper.HasHypergeometricAntidifference
        (toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom)) := by
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_specialize_data backend hbackend f hK P Q r hrun hP hQ hV
  have hA : A ≠ 0 := fun hz => hvalid.1.1 (by simp [hz])
  have hB0 : B ≠ 0 := fun hz => hvalid.1.2.1 (by simp [hz])
  have hB : taylor (-1 : K) B ≠ 0 := (taylor_eq_zero _ _).not.mpr hB0
  rw [gosperSolve_specialize_complete backend.solver hbackend.solver
    A (taylor (-1) B) C f hK r hsolve hA hB]
  simpa using (normalForm_hypergeometric_iff_polynomial
    (P.map f.toRingHom) (Q.map f.toRingHom) hP hQ _ hvalid).symm

/-- Interpret a specialized output as the two endpoints of a finite sum. -/
theorem gosperTerm_specialize_sum (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok (some r))
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
  have hv := gosperTerm_specialize_verified backend hbackend f hK P Q r hrun
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
