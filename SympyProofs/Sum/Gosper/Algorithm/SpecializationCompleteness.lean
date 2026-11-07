module

public import SympyProofs.Sum.Gosper.Algorithm.Completeness
public import SympyProofs.Sum.Gosper.Algorithm.SpecializationCorrectness

/-! Completeness after parameter specialization, characterized by the vanishing
residual polynomial. -/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

attribute [local instance 2000] Ring.toIntAlgebra

open Polynomial IsLocalization

variable {K : Type} [CommRing K] [IsDomain K] [DecidableEq K] [Div K]
variable {L : Type} [CommRing L] [IsDomain L] [Algebra K L] [Div L]
variable [MulDivCancelClass K] [MulDivCancelClass L]
variable (backend : TermBackend K L)

variable {E : Type} [Field E] [Algebra K E]

/-- The evaluated residual characterizes summability of the specialized input.
The successful run supplies coefficient descent; callers need no normal-form hypotheses. -/
theorem gosperTerm_specialize_complete [CharZero K] [CharZero E]
    (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    r.residual.map f.toRingHom = 0 ↔
      Gosper.HasHypergeometricAntidifference
        (toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom)) := by
  obtain ⟨A, B, C, hsolve, hvalid⟩ :=
    gosperTerm_specialize_normalForm backend hbackend f hK P Q r hrun hP hQ hV
  have hA : A ≠ 0 := fun hz => hvalid.1.1 (by simp [hz])
  have hB0 : B ≠ 0 := fun hz => hvalid.1.2.1 (by simp [hz])
  have hB : taylor (-1 : K) B ≠ 0 := (taylor_eq_zero _ _).not.mpr hB0
  rw [gosperSolve_specialize_complete backend hbackend
    A (taylor (-1) B) C f hK r hsolve hA hB]
  simpa using (normalForm_hypergeometric_iff_polynomial
    (P.map f.toRingHom) (Q.map f.toRingHom) hP hQ _ hvalid).symm

/-- A specialized residual vanishes exactly when the specialized input is summable. -/
theorem gosperTerm_specialize_residual_complete [CharZero K] [CharZero E]
    (hbackend : backend.Valid)
    (f : L →ₐ[K] E) (hK : Function.Injective (algebraMap K E))
    (P Q : L[X]) (r : Result L)
    (hrun : gosperTerm backend P Q = .ok r)
    (hP : P.map f.toRingHom ≠ 0) (hQ : Q.map f.toRingHom ≠ 0)
    (hV : r.denominator.map f.toRingHom ≠ 0) :
    r.residual.map f.toRingHom = 0 ↔
      Gosper.HasHypergeometricAntidifference
        (toRatFunc (P.map f.toRingHom) (Q.map f.toRingHom)) := by
  exact gosperTerm_specialize_complete backend hbackend f hK P Q r hrun hP hQ hV

end Gosper.Algorithm
