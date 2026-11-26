module

public import SympyProofs.Calculus.Antiderivative.Proof.Step.Hermite
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! The normal denominator for an exponential step retains exactly the simple normal factors. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- The exponential cofactor is squarefree and omits the special prime X, including
when the original denominator has a higher-order zero at X = 0. -/
theorem expNormalDen_spec {q : Poly F} (hq : q ≠ 0) :
    let s := Poly.equiv (q / gcd q (Poly.X * q.derivative))
    Squarefree s ∧ ¬ X ∣ s := by
  classical
  let r := gcd q q.derivative
  let d := gcd q (Poly.X * q.derivative)
  let s := q / d
  have hd : d ≠ 0 := by simp [d, gcd_eq_zero_iff, hq]
  have hr : r ≠ 0 := by simp [r, gcd_eq_zero_iff, hq]
  have hdq : d * s = q := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left ..)
  have hrq : r * (q / r) = q := EuclideanDomain.mul_div_cancel' hr (gcd_dvd_left ..)
  have hrd : r ∣ d := dvd_gcd (gcd_dvd_left ..) (dvd_mul_of_dvd_right (gcd_dvd_right ..) _)
  have hsd : s ∣ q / r := by
    obtain ⟨a,ha⟩ := hrd
    refine ⟨a,mul_left_cancel₀ hr ?_⟩
    rw [hrq, ← hdq, ha]
    ring
  refine ⟨(squarefreeParts_spec hq).squarefree_of_dvd (map_dvd Poly.equiv hsd), ?_⟩
  let Q := Poly.equiv q
  let m := multiplicity X Q
  have hQ : Q ≠ 0 := (map_ne_zero_iff _ Poly.equiv.injective).mpr hq
  have hpow : X ^ m ∣ Q := pow_multiplicity_dvd X Q
  have hder : X ^ m ∣ X * Q.derivative := by
    cases hm : m with
    | zero => simp
    | succ j =>
      have h := pow_sub_one_dvd_derivative_of_pow_dvd (hm ▸ hpow : X ^ (j+1) ∣ Q)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (by simpa using h)
  have hfactor : X ^ m ∣ Poly.equiv d := by
    apply dvd_trans _ (Poly.associated_equiv_gcd q _).symm.dvd
    exact dvd_gcd hpow (by simpa [Q] using hder)
  intro hx
  have over : X ^ (m+1) ∣ Q := by
    rw [pow_succ, ← show Poly.equiv d * Poly.equiv s = Q from
      (map_mul Poly.equiv d s).symm.trans (congrArg Poly.equiv hdq)]
    exact mul_dvd_mul hfactor hx
  have := (FiniteMultiplicity.of_prime_left prime_X hQ).pow_dvd_iff_le_multiplicity.mp over
  change m+1 ≤ m at this
  omega

end SympyProofs.Calculus.Antiderivative.Step
