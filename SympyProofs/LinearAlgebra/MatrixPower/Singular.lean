module

public import SympyProofs.LinearAlgebra.MatrixPower.General

/-!
# Singular matrices and the domain of complex powers

Natural powers always make sense. For other exponents the zero primary
component requires enough regularity at zero; a nilpotency bound `m` gives
the standard sufficient condition `m - 1 < re z`. A semisimple zero eigenvalue
has `m = 1`, so every exponent with positive real part is admissible.

The zero-jet convention is explicit even outside that domain. In particular
it must not be interpreted as a square root of a nonzero nilpotent block.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem MatrixPowerDefined.of_zero_primary_pow_eq_zero (A : Matrix n n ℂ) (z : ℂ)
    (m : ℕ) (hm : 0 < m)
    (hA : (primaryEnd (Matrix.toLinAlgEquiv' A) 0) ^ m = 0)
    (hz : (m : ℝ) - 1 < z.re) : MatrixPowerDefined A z :=
  Or.inr (fun _ => ⟨m, hm, hA, hz⟩)

theorem MatrixPowerDefined.of_zero_primary_eq_zero (A : Matrix n n ℂ) (z : ℂ)
    (hA : primaryEnd (Matrix.toLinAlgEquiv' A) 0 = 0) (hz : 0 < z.re) :
    MatrixPowerDefined A z := by
  apply MatrixPowerDefined.of_zero_primary_pow_eq_zero A z 1 (by decide)
  · simpa using hA
  · simpa using hz

/-- A dimension bound suffices, even without computing the zero Jordan blocks. -/
theorem MatrixPowerDefined.of_finrank_lt_re (A : Matrix n n ℂ) (z : ℂ)
    (hz : (Module.finrank ℂ (n → ℂ) : ℝ) < z.re) : MatrixPowerDefined A z := by
  apply MatrixPowerDefined.of_zero_primary_pow_eq_zero A z
    (Module.finrank ℂ (n → ℂ) + 1) (Nat.succ_pos _)
  · have hn : IsNilpotent (primaryEnd (Matrix.toLinAlgEquiv' A) 0) := by
      convert primaryEnd_nilpotent (Matrix.toLinAlgEquiv' A) 0 using 1
      ext x
      simp
    exact pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
      (nilpotent_pow_finrank hn)
  · simpa using hz

theorem primaryEnd_diagonal_zero (d : n → ℂ) :
    primaryEnd (Matrix.toLinAlgEquiv' (Matrix.diagonal d)) 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Matrix.toLin' (Matrix.diagonal d) x = 0
  have hx := x.property
  change (x : n → ℂ) ∈ End.maxGenEigenspace (Matrix.toLin' (Matrix.diagonal d)) 0 at hx
  rw [Matrix.maxGenEigenspace_toLin'_diagonal_eq_eigenspace, End.mem_eigenspace_iff] at hx
  simpa using hx

theorem MatrixPowerDefined.diagonal (d : n → ℂ) (z : ℂ) (hz : 0 < z.re) :
    MatrixPowerDefined (Matrix.diagonal d) z :=
  MatrixPowerDefined.of_zero_primary_eq_zero _ _ (primaryEnd_diagonal_zero d) hz

/-- Non-natural powers of a nilpotent matrix use the zero jets at zero.
This is a genuine primary power on the admissible domain, and a convention
otherwise; it does not assert a root identity. -/
theorem matrixCpow_of_isNilpotent (A : Matrix n n ℂ) (hA : IsNilpotent A) (z : ℂ)
    (hz : ¬∃ k : ℕ, z = (k : ℂ)) : matrixCpow A z = 0 := by
  nontriviality (Matrix n n ℂ)
  have hs : ∀ a ∈ spectrum ℂ A, a = 0 := by
    obtain ⟨k, hk⟩ := hA
    intro a ha
    have h := spectrum.pow_mem_pow A k ha
    rw [hk, spectrum.zero_eq, Set.mem_singleton_iff] at h
    exact eq_zero_of_pow_eq_zero h
  have h : matrixCpow A z = aeval A (0 : ℂ[X]) := by
    apply matrixCpow_eq_aeval
    intro a ha
    rw [hs a ha, localCpowPolynomial_zero, zeroPowerPolynomial_of_not_natCast z hz, sub_self]
    exact dvd_zero _
  simpa using h

end SympyProofs.MatrixExponential
