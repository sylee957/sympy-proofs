module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Interpolation of local matrix functions

The Chinese remainder theorem glues polynomial expressions at finitely many
eigenvalues. Congruences modulo powers of `X - λ` preserve the nilpotent data,
so these results apply to arbitrary matrices, not just diagonalizable ones.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

theorem exists_primaryInterpolation {s : Set ℂ} (hs : s.Finite) (d : ℕ)
    (q : ℂ → ℂ[X]) :
    ∃ p : ℂ[X], ∀ z ∈ s, (X - C z) ^ d ∣ p - q z := by
  let : Finite s := hs.to_subtype
  let I : s → Ideal ℂ[X] := fun z => Ideal.span {(X - C (z : ℂ)) ^ d}
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro a b hab
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr (fun h => hab (Subtype.ext h))).isUnit).pow
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun z => q z)
  exact ⟨p, fun z hz => Ideal.mem_span_singleton.mp (hp ⟨z, hz⟩)⟩

theorem aeval_eq_of_dvd_sub {A : Type*} [Ring A] [Algebra ℂ A]
    (a : A) (z : ℂ) (d : ℕ) {p q : ℂ[X]}
    (h : (X - C z) ^ d ∣ p - q)
    (hn : (a - algebraMap ℂ A z) ^ d = 0) : aeval a p = aeval a q := by
  obtain ⟨r, hr⟩ := h
  apply sub_eq_zero.mp
  rw [← map_sub, hr, map_mul, map_pow, map_sub, aeval_X, aeval_C, hn, zero_mul]

end SympyProofs.MatrixExponential
