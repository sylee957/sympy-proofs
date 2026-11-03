module

public import SympyProofs.Sum.Gosper.Algorithm.Correctness
public import SympyProofs.Sum.Gosper.Algorithm.NormalizationSpecialization

/-! Soundness and finite-sum identities after parameter specialization,
including the retained remainder. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {K : Type} [CommRing K] [IsDomain K] [DecidableEq K]
variable {L : Type} [CommRing L] [IsDomain L] [Algebra K L]
variable (backend : TermBackend K L)

/-- The polynomial reduction survives every coefficient homomorphism. -/
theorem gosperTerm_specialize_reduction_identity {E : Type*} [CommRing E]
    (hbackend : backend.Valid) (f : L →+* E)
    (P Q : L[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r) :
    residual (P.map f) (Q.map f) (r.numerator.map f) (r.denominator.map f) =
      -(Q.map f * taylor 1 (r.denominator.map f) * r.residual.map f) := by
  have he := congrArg (Polynomial.map f)
    (gosperTerm_reduction_identity backend hbackend P Q hP hQ r hrun).2.2
  simpa only [residual_map, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_taylor, map_one] using he

/-- Specializing parameters preserves the rational reduction whenever the two
denominators remain nonzero. The parameter map need not be injective. -/
theorem gosperTerm_specialize_reduction {E : Type*} [Field E]
    (hbackend : backend.Valid) (f : L →+* E)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hQ : Q.map f ≠ 0) (hV : r.denominator.map f ≠ 0) :
    toRatFunc (P.map f) (Q.map f) *
        Gosper.rationalShift 1 (toRatFunc (r.numerator.map f) (r.denominator.map f)) -
      toRatFunc (r.numerator.map f) (r.denominator.map f) +
      toRatFunc (r.residual.map f) (r.denominator.map f) = 1 := by
  exact reduction_ratFunc _ _ _ _ _ hQ hV
    (gosperTerm_specialize_reduction_identity backend hbackend f P Q hP0 hQ0 r hrun)

/-- Reconstruct a specialized finite sum as two endpoint values plus the
sum of the actual residual terms. -/
theorem gosperTerm_specialize_reduction_sum {E : Type*} [Field E]
    (hbackend : backend.Valid) (f : L →+* E)
    (P Q : L[X]) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (a : ℕ → E) (m n : ℕ) (hmn : m ≤ n)
    (hQ : ∀ k ∈ Finset.Ico m n, (Q.map f).eval (k : E) ≠ 0)
    (hV : ∀ k ∈ Finset.Icc m n, (r.denominator.map f).eval (k : E) ≠ 0)
    (hratio : ∀ k ∈ Finset.Ico m n,
      a (k + 1) * (Q.map f).eval (k : E) = a k * (P.map f).eval (k : E)) :
    ∑ k ∈ Finset.Ico m n, a k =
      a n * ((r.numerator.map f).eval (n : E) / (r.denominator.map f).eval (n : E)) -
        a m * ((r.numerator.map f).eval (m : E) / (r.denominator.map f).eval (m : E)) +
        ∑ k ∈ Finset.Ico m n,
          a k * ((r.residual.map f).eval (k : E) / (r.denominator.map f).eval (k : E)) := by
  exact reduction_sum _ _ _ _ _
    (gosperTerm_specialize_reduction_identity backend hbackend f P Q hP0 hQ0 r hrun)
    a m n hmn hQ hV hratio

variable {E : Type} [Field E] [Algebra K E]

/-- Recover the constant-domain solver and its specialized normal form from the full run. -/
theorem gosperTerm_specialize_normalForm (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    ∃ A B : K[X], ∃ C : L[X],
      gosperSolve backend A (taylor (-1) B) C = r ∧
      normalFormValid (P.map f.toRingHom) (Q.map f.toRingHom)
        (A.map (algebraMap K E), B.map (algebraMap K E), C.map f.toRingHom) := by
  have hP0 : P ≠ 0 := fun hz => hP (by simp [hz])
  have hQ0 : Q ≠ 0 := fun hz => hQ (by simp [hz])
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_normalForm backend hbackend P Q hP0 hQ0 r hrun
  obtain ⟨δ, _, hden⟩ := gosperSolve_denominator backend hbackend
    A (taylor (-1) B) C r hsolve
  have hC : C.map f.toRingHom ≠ 0 := by
    intro hzero
    apply hV
    rw [hden]
    rw [Polynomial.map_mul, hzero, mul_zero]
  refine ⟨A, B, C, hsolve, ?_⟩
  have hKi : Function.Injective (algebraMap K (FractionRing L)) := by
    rw [IsScalarTower.algebraMap_eq K L (FractionRing L)]
    exact (IsFractionRing.injective L (FractionRing L)).comp hbackend.algebraMap_injective
  exact normalFormValid_specialize (IsScalarTower.toAlgHom K L (FractionRing L))
    (IsFractionRing.injective L (FractionRing L)) f hKi hK
    A B C P Q hvalid hC

/-- A vanishing specialized residual verifies the specialized input, even when
the generic residual does not vanish or evaluation lowers the numerator degree. -/
theorem gosperTerm_specialize_verified [DecidableEq E] (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : r.residual.map f.toRingHom = 0) :
    verify (P.map f.toRingHom) (Q.map f.toRingHom)
      (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = true := by
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_specialize_normalForm backend hbackend f hK P Q r hrun hP hQ hV
  obtain ⟨δ, hδ, x, hu, hd, hx⟩ := gosperSolve_specialize_sound backend hbackend
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
    (hrun : gosperTerm backend P Q = .ok r)
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0)
    (hzero : r.residual.map f.toRingHom = 0) :
    toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom) *
        Gosper.rationalShift 1
          (toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom)) -
      toRatFunc (r.numerator.map f.toRingHom) (r.denominator.map f.toRingHom) = 1 := by
  classical
  exact verify_ratFunc _ _ _ _
    (gosperTerm_specialize_verified backend hbackend f hK P Q r hrun hP hQ hV hzero)

/-- Interpret a specialized output as the two endpoints of a finite sum. -/
theorem gosperTerm_specialize_sum (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hP0 : P.map f.toRingHom ≠ 0) (hQ0 : Q.map f.toRingHom ≠ 0)
    (hV0 : r.denominator.map f.toRingHom ≠ 0)
    (hzero : r.residual.map f.toRingHom = 0)
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
