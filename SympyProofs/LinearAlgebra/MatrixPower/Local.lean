module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.LocalLogarithm
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Local polynomials for complex powers

At a nonzero eigenvalue, exponentiate the finite local logarithm. At zero,
natural exponents use the polynomial `X^k`; other exponents use zero jets.
The latter are the genuine limiting jets when `re z > m - 1`, where `m` is
the size of the largest Jordan block at zero. Outside that domain they are
an explicit totalization convention, not a claim that matrix roots exist.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

/-- The local polynomial on the zero primary component. -/
noncomputable def zeroPowerPolynomial (z : ℂ) : ℂ[X] := by
  classical
  exact if h : ∃ k : ℕ, z = (k : ℂ) then X ^ h.choose else 0

@[simp] theorem zeroPowerPolynomial_natCast (k : ℕ) :
    zeroPowerPolynomial (k : ℂ) = X ^ k := by
  classical
  have h : ∃ j : ℕ, (k : ℂ) = (j : ℂ) := ⟨k, rfl⟩
  have hk : h.choose = k := by exact_mod_cast h.choose_spec.symm
  simp only [zeroPowerPolynomial, dite_eq_left h, hk]

theorem zeroPowerPolynomial_of_not_natCast (z : ℂ)
    (hz : ¬∃ k : ℕ, z = (k : ℂ)) : zeroPowerPolynomial z = 0 := by
  simp only [zeroPowerPolynomial, dite_eq_right hz]

/-- Finite Taylor data for the selected power at an eigenvalue. -/
noncomputable def localCpowPolynomial (a z : ℂ) (d : ℕ) : ℂ[X] :=
  if a = 0 then zeroPowerPolynomial z else
    C (a ^ z) * ∑ k ∈ Finset.range d,
      (k.factorial : ℚ)⁻¹ • (C z * (localLogPolynomial a d - C (Complex.log a))) ^ k

@[simp] theorem localCpowPolynomial_zero (z : ℂ) (d : ℕ) :
    localCpowPolynomial 0 z d = zeroPowerPolynomial z := by
  simp [localCpowPolynomial]

theorem localCpowPolynomial_eval (a z : ℂ) (d : ℕ) (hd : d ≠ 0) :
    (localCpowPolynomial a z d).eval a = a ^ z := by
  classical
  by_cases ha : a = 0
  · subst a
    by_cases hz : ∃ k : ℕ, z = (k : ℂ)
    · obtain ⟨k, rfl⟩ := hz
      simp [Complex.cpow_natCast]
    · have hz0 : z ≠ 0 := fun h => hz ⟨0, by simpa using h⟩
      simp [zeroPowerPolynomial_of_not_natCast z hz, Complex.zero_cpow hz0]
  · simp only [localCpowPolynomial, ite_eq_right ha, eval_mul, eval_C,
      eval_finsetSum, eval_smul, eval_pow, eval_sub, localLogPolynomial_eval,
      sub_self, mul_zero]
    have hs : (∑ k ∈ Finset.range d, (k.factorial : ℚ)⁻¹ • (0 : ℂ) ^ k) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [zero_pow hk0]
      · intro h
        exact (h (Finset.mem_range.mpr (Nat.pos_of_ne_zero hd))).elim
    rw [hs, mul_one]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem aeval_localCpowPolynomial_of_ne_zero (f : End ℂ V) (a z : ℂ) (d : ℕ)
    (hd : Module.finrank ℂ V ≤ d) (ha : a ≠ 0) (hn : (f - a • 1) ^ d = 0) :
    aeval f (localCpowPolynomial a z d) =
      endExp (z • aeval f (localLogPolynomial a d)) := by
  have hN : IsNilpotent (a⁻¹ • (f - a • 1)) :=
    (show IsNilpotent (f - a • 1) from ⟨d, hn⟩).smul a⁻¹
  have hL := (Nilpotent.isNilpotent_log hN).smul z
  have hpow := pow_eq_zero_of_le hd (nilpotent_pow_finrank hL)
  have he : aeval f (localLogPolynomial a d) =
      Complex.log a • 1 + Nilpotent.log (a⁻¹ • (f - a • 1)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      aeval_localLogPolynomial f a d (by
        simpa only [Algebra.algebraMap_eq_smul_one] using hn)
  rw [localCpowPolynomial, ite_eq_right ha, map_mul, aeval_C, map_sum, he,
    smul_add, smul_smul, endExp_scalar_add, endExp_eq_of_nilpotent hL,
    IsNilpotent.exp_eq_sum hpow]
  rw [Complex.cpow_def_of_ne_zero ha, mul_comm (Complex.log a) z,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [map_rat_smul, map_pow, map_mul, map_sub, aeval_C, he,
    Algebra.algebraMap_eq_smul_one, add_sub_cancel_left, smul_mul_assoc, one_mul]

theorem aeval_localCpowPolynomial_natCast (f : End ℂ V) (a : ℂ) (k d : ℕ)
    (hd : Module.finrank ℂ V ≤ d) (hn : (f - a • 1) ^ d = 0) :
    aeval f (localCpowPolynomial a (k : ℂ) d) = f ^ k := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [aeval_localCpowPolynomial_of_ne_zero f a k d hd ha hn,
      endExp_natCast_smul, endExp_localLogPolynomial f a d ha hn]

end SympyProofs.MatrixExponential
