module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Poles of a solution of `Y′ + (N/B) Y = H/T` in `F(θ)`, for a derivation of `F[θ]`
(Risch 1969, pp. 186–187), at primes that are normal for the derivation. A pole of the
solution deeper than that of the right-hand side forces a simple pole of the coefficient
whose residue is the order of the pole. A bound on those orders gives one denominator for
every solution. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension

open Polynomial

namespace Pole

section Abstract

variable {F : Type*} [Field F] [CharZero F]

/-- The differential equation with unknown `u/d`, cleared of denominators. -/
def Equation (δ : Derivation ℤ F[X] F[X]) (N B H T u d : F[X]) : Prop :=
  ((δ u * d - u * δ d) * B + N * u * d) * T = H * d ^ 2 * B

omit [CharZero F] in
/-- The numerator of the derivative of `u / (s ^ (j + 1) * t)` is divisible by `s ^ j`. -/
theorem derivative_at_pole (δ : Derivation ℤ F[X] F[X]) (s u t : F[X]) (j : ℕ) :
    δ u * (s ^ (j+1) * t) - u * δ (s ^ (j+1) * t) =
      s ^ j * ((δ u * t - u * δ t) * s - u * C ((j+1 : ℕ) : F) * δ s * t) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Nat.add_sub_cancel, map_natCast]
  rw [pow_succ]
  push_cast
  ring

/-- At a normal prime where the right-hand side has too small a pole, the coefficient has a
pole and equals the solution's pole order times the logarithmic derivative there. -/
theorem order_or_residue (δ : Derivation ℤ F[X] F[X]) {N B H T u d s : F[X]} (hs : Prime s)
    (normal : ¬ s ∣ δ s) (hT : T ≠ 0) (hd : d ≠ 0) (hu : IsRelPrime u d)
    (he : Equation δ N B H T u d) :
    multiplicity s d ≤ multiplicity s T ∨
      (s ∣ B ∧ s ∣ N - C (multiplicity s d : F) * δ B) := by
  by_cases hle : multiplicity s d ≤ multiplicity s T
  · exact Or.inl hle
  right
  obtain ⟨t, ht, hst⟩ := (FiniteMultiplicity.of_prime_left hs hd).exists_eq_pow_mul_and_not_dvd
  generalize hj : multiplicity s d = j at ht hle ⊢
  cases j with
  | zero => omega
  | succ j =>
    have hsd : s ∣ d := ht ▸ dvd_mul_of_dvd_left (dvd_pow_self s (Nat.succ_ne_zero j)) _
    have hsu : ¬s ∣ u := fun h => hs.not_isUnit (hu h hsd)
    have sc : ¬s ∣ C ((j+1 : ℕ) : F) := fun h => hs.not_isUnit (isUnit_of_dvd_unit h
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)))))
    obtain ⟨a, ha⟩ : ∃ a : F[X], a = (δ u * t - u * δ t) * s - u * C ((j+1 : ℕ) : F) * δ s * t :=
      ⟨_, rfl⟩
    have hna : ¬s ∣ a := by
      intro h
      have e := dvd_sub (dvd_mul_left s (δ u * t - u * δ t)) h
      rw [ha, sub_sub_cancel] at e
      simp only [hs.dvd_mul, hsu, sc, normal, hst, or_self] at e
    obtain ⟨w, hw⟩ : ∃ w : F[X], w = a * B + N * u * s * t := ⟨_, rfl⟩
    have key : w * T = H * s ^ (j+2) * t ^ 2 * B := by
      apply mul_left_cancel₀ (pow_ne_zero j hs.ne_zero)
      unfold Equation at he
      rw [ht, derivative_at_pole, ← ha] at he
      rw [hw]
      simp only [pow_succ] at he ⊢
      linear_combination he
    obtain ⟨v, hv, hsv⟩ := (FiniteMultiplicity.of_prime_left hs hT).exists_eq_pow_mul_and_not_dvd
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = multiplicity s T := ⟨_, rfl⟩
    rw [← hm] at hv hle
    have hmj : m ≤ j := by omega
    have sq : s ^ 2 ∣ w := by
      apply hs.pow_dvd_of_dvd_mul_right _ hsv
      refine ⟨H * s ^ (j-m) * t ^ 2 * B, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero m hs.ne_zero)
      have ar : j + 2 = m + 2 + (j - m) := by omega
      rw [hv, ar, pow_add, pow_add] at key
      linear_combination key
    have first : s ∣ B := by
      have hw' : s ∣ w := (dvd_pow_self s (by decide : 2 ≠ 0)).trans sq
      have hu' : s ∣ N * u * s * t := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      rw [hw] at hw'
      exact (hs.dvd_mul.mp ((dvd_add_left hu').mp hw')).resolve_left hna
    obtain ⟨b, hb⟩ := first
    refine ⟨⟨b, hb⟩, ?_⟩
    have second : s ∣ a * b + N * u * t := by
      obtain ⟨e, he'⟩ := sq
      refine ⟨e, mul_left_cancel₀ hs.ne_zero ?_⟩
      rw [hw, hb] at he'
      linear_combination he'
    have sd : s ∣ u * t * (N - C ((j+1 : ℕ) : F) * δ B) := by
      obtain ⟨e, he'⟩ := second
      refine ⟨e - (δ u * t - u * δ t) * b - u * t * C ((j+1 : ℕ) : F) * δ b, ?_⟩
      rw [hb, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [ha] at he'
      linear_combination he'
    exact (hs.dvd_mul.mp sd).resolve_left (fun h => (hs.dvd_mul.mp h).elim hsu hst)

/-- A uniform bound on integral residues gives one denominator for all solutions. -/
theorem denominator_dvd (δ : Derivation ℤ F[X] F[X]) {N B H T u d : F[X]}
    (normal : ∀ s : F[X], Prime s → ¬ s ∣ δ s) (hB : B ≠ 0) (hT : T ≠ 0) (hd : d ≠ 0)
    (hu : IsRelPrime u d) (he : Equation δ N B H T u d) (bound : ℕ)
    (res : ∀ (s : F[X]) (m : ℕ), Prime s → s ∣ B → s ∣ N - C (m : F) * δ B → m ≤ bound) :
    d ∣ T * B ^ bound := by
  have hn := mul_ne_zero hT (pow_ne_zero bound hB)
  apply (UniqueFactorizationMonoid.dvd_iff_multiplicity_le hd hn).mpr
  intro s hs
  rw [← (FiniteMultiplicity.of_prime_left hs hn).pow_dvd_iff_le_multiplicity]
  rcases order_or_residue δ hs (normal s hs) hT hd hu he with le | ⟨hb, hr⟩
  · exact dvd_mul_of_dvd_left
      ((FiniteMultiplicity.of_prime_left hs hT).pow_dvd_iff_le_multiplicity.mpr le) _
  · apply dvd_mul_of_dvd_right _ T
    exact (pow_dvd_pow_of_dvd hb _).trans (pow_dvd_pow B (res s _ hs hb hr))

end Abstract

end Pole

end SympyProofs.Calculus.Antiderivative.Extension
