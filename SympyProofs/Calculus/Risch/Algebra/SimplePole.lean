module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rational functions with at most simple poles, and rational functions vanishing at
infinity. A logarithmic derivative has at most simple poles, and the derivative of a rational
function with a pole at a normal prime has a multiple pole there. Whether a combination of
fractions over one denominator has at most simple poles is a divisibility by the greatest
common divisor of that denominator and its derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.SimplePole

open Polynomial

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- No pole at `p`. -/
def Integral (p : F[X]) (y : RatFunc F) : Prop := ∃ N D : F[X], ¬ p ∣ D ∧ y * ι D = ι N

/-- At most a simple pole at every prime. -/
def Simple (y : RatFunc F) : Prop := ∀ p : F[X], Prime p → Integral p (ι p * y)

/-- A proper fraction. -/
def Proper (y : RatFunc F) : Prop := ∃ N D : F[X], N.degree < D.degree ∧ y * ι D = ι N

section Integral

variable {p q : F[X]} {y z : RatFunc F}

theorem integral_algebraMap (hp : Prime p) (P : F[X]) : Integral p (ι P) :=
  ⟨P, 1, fun h => hp.not_isUnit (isUnit_of_dvd_one h), by simp⟩

theorem Integral.add (hp : Prime p) (hy : Integral p y) (hz : Integral p z) :
    Integral p (y + z) := by
  obtain ⟨N₁, D₁, h₁, e₁⟩ := hy
  obtain ⟨N₂, D₂, h₂, e₂⟩ := hz
  refine ⟨N₁ * D₂ + N₂ * D₁, D₁ * D₂, fun h => (hp.dvd_or_dvd h).elim h₁ h₂, ?_⟩
  simp only [map_mul, map_add]
  rw [← e₁, ← e₂]
  ring

theorem Integral.neg (hy : Integral p y) : Integral p (-y) := by
  obtain ⟨N, D, h, e⟩ := hy
  exact ⟨-N, D, h, by rw [map_neg, ← e]; ring⟩

theorem Integral.sub (hp : Prime p) (hy : Integral p y) (hz : Integral p z) :
    Integral p (y - z) := by
  rw [sub_eq_add_neg]
  exact hy.add hp hz.neg

theorem Integral.mul (hp : Prime p) (hy : Integral p y) (hz : Integral p z) :
    Integral p (y * z) := by
  obtain ⟨N₁, D₁, h₁, e₁⟩ := hy
  obtain ⟨N₂, D₂, h₂, e₂⟩ := hz
  refine ⟨N₁ * N₂, D₁ * D₂, fun h => (hp.dvd_or_dvd h).elim h₁ h₂, ?_⟩
  simp only [map_mul]
  rw [← e₁, ← e₂]
  ring

/-- Associated primes have the same integral elements. -/
theorem Integral.of_dvd (hp : Prime p) (hq : Prime q) (h : p ∣ q) (hy : Integral q y) :
    Integral p y := by
  obtain ⟨N, D, hD, e⟩ := hy
  exact ⟨N, D, fun hpD => hD ((hp.irreducible.dvd_symm hq.irreducible h).trans hpD), e⟩

theorem integral_iff_denom (hp : Prime p) : Integral p y ↔ ¬ p ∣ y.denom := by
  have hden0 : ι y.denom ≠ 0 := RatFunc.algebraMap_ne_zero y.denom_ne_zero
  have hy : ι y.num = y * ι y.denom := (div_eq_iff hden0).1 (RatFunc.num_div_denom y)
  constructor
  · rintro ⟨N, D, hD, e⟩ hden
    have e' : y.num * D = N * y.denom := by
      apply RatFunc.algebraMap_injective F
      simp only [map_mul]
      rw [hy, ← e]
      ring
    have hnum : p ∣ y.num :=
      (hp.dvd_or_dvd (e' ▸ Dvd.dvd.mul_left hden N)).resolve_right hD
    exact hp.not_isUnit ((RatFunc.isCoprime_num_denom y).isUnit_of_dvd' hnum hden)
  · intro h
    exact ⟨y.num, y.denom, h, hy.symm⟩

/-- A fraction without a pole at `p` whose denominator is divisible by a power of `p` has
its numerator divisible by that power. -/
theorem Integral.pow_dvd (hp : Prime p) {W T : F[X]} (hT : T ≠ 0) {k : ℕ}
    (hy : Integral p (ι W / ι T)) (hk : p ^ k ∣ T) : p ^ k ∣ W := by
  obtain ⟨N, D, hD, e⟩ := hy
  have hT' : ι T ≠ 0 := RatFunc.algebraMap_ne_zero hT
  have e' : W * D = N * T := by
    apply RatFunc.algebraMap_injective F
    simp only [map_mul]
    rw [← e]
    field_simp
  exact hp.pow_dvd_of_dvd_mul_right k hD (e' ▸ hk.mul_left N)

/-- The same with at most a simple pole. -/
theorem Integral.pow_dvd_of_mul (hp : Prime p) {W T : F[X]} (hT : T ≠ 0) {k : ℕ}
    (hy : Integral p (ι p * (ι W / ι T))) (hk : p ^ (k + 1) ∣ T) : p ^ k ∣ W := by
  obtain ⟨N, D, hD, e⟩ := hy
  have hT' : ι T ≠ 0 := RatFunc.algebraMap_ne_zero hT
  have e' : p * (W * D) = N * T := by
    apply RatFunc.algebraMap_injective F
    simp only [map_mul]
    rw [← e]
    field_simp
  obtain ⟨c, rfl⟩ := hk
  have e'' : W * D = p ^ k * (N * c) := by
    apply mul_left_cancel₀ hp.ne_zero
    rw [e']
    ring
  exact hp.pow_dvd_of_dvd_mul_right k hD ⟨_, e''⟩

end Integral

section Simple

variable {y z : RatFunc F}

theorem Simple.of_integral (h : ∀ p : F[X], Prime p → Integral p y) : Simple y :=
  fun p hp => (integral_algebraMap hp p).mul hp (h p hp)

theorem simple_zero : Simple (0 : RatFunc F) :=
  Simple.of_integral fun p hp => by simpa using integral_algebraMap hp 0

theorem simple_algebraMap (P : F[X]) : Simple (ι P) :=
  Simple.of_integral fun _ hp => integral_algebraMap hp P

theorem Simple.add (hy : Simple y) (hz : Simple z) : Simple (y + z) := by
  intro p hp
  rw [mul_add]
  exact (hy p hp).add hp (hz p hp)

theorem Simple.neg (hy : Simple y) : Simple (-y) := by
  intro p hp
  rw [mul_neg]
  exact (hy p hp).neg

theorem Simple.sub (hy : Simple y) (hz : Simple z) : Simple (y - z) := by
  rw [sub_eq_add_neg]
  exact hy.add hz.neg

theorem Simple.C_mul (c : F) (hy : Simple y) : Simple (RatFunc.C c * y) := by
  intro p hp
  have e : ι p * (RatFunc.C c * y) = ι (C c) * (ι p * y) := by
    rw [RatFunc.algebraMap_C]
    ring
  rw [e]
  exact (integral_algebraMap hp _).mul hp (hy p hp)

end Simple

section Proper

variable {y z : RatFunc F}

private theorem degree_mul_lt_mul {N D E : F[X]} (h : N.degree < D.degree) (hE : E ≠ 0) :
    (N * E).degree < (D * E).degree := by
  rw [degree_mul, degree_mul]
  exact WithBot.add_lt_add_right (degree_ne_bot.2 hE) h

private theorem ne_zero_of_degree_lt {N D : F[X]} (h : N.degree < D.degree) : D ≠ 0 := by
  rintro rfl
  simp at h

theorem proper_zero : Proper (0 : RatFunc F) :=
  ⟨0, 1, by simp, by simp⟩

theorem proper_div {N D : F[X]} (h : N.degree < D.degree) : Proper (ι N / ι D) :=
  ⟨N, D, h, div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero (ne_zero_of_degree_lt h))⟩

theorem Proper.add (hy : Proper y) (hz : Proper z) : Proper (y + z) := by
  obtain ⟨N₁, D₁, h₁, e₁⟩ := hy
  obtain ⟨N₂, D₂, h₂, e₂⟩ := hz
  have hD₁ : D₁ ≠ 0 := ne_zero_of_degree_lt h₁
  have hD₂ : D₂ ≠ 0 := ne_zero_of_degree_lt h₂
  refine ⟨N₁ * D₂ + N₂ * D₁, D₁ * D₂, ?_, ?_⟩
  · refine (degree_add_le _ _).trans_lt (max_lt (degree_mul_lt_mul h₁ hD₂) ?_)
    rw [mul_comm D₁ D₂]
    exact degree_mul_lt_mul h₂ hD₁
  · simp only [map_mul, map_add]
    rw [← e₁, ← e₂]
    ring

theorem Proper.neg (hy : Proper y) : Proper (-y) := by
  obtain ⟨N, D, h, e⟩ := hy
  exact ⟨-N, D, by rwa [degree_neg], by rw [map_neg, ← e]; ring⟩

theorem Proper.sub (hy : Proper y) (hz : Proper z) : Proper (y - z) := by
  rw [sub_eq_add_neg]
  exact hy.add hz.neg

theorem Proper.C_mul (c : F) (hy : Proper y) : Proper (RatFunc.C c * y) := by
  obtain ⟨N, D, h, e⟩ := hy
  by_cases hc : c = 0
  · subst hc
    simpa using proper_zero (F := F)
  · exact ⟨C c * N, D, by rwa [degree_C_mul hc],
      by rw [map_mul, RatFunc.algebraMap_C, ← e]; ring⟩

/-- The only proper polynomial is zero. -/
theorem proper_algebraMap_iff {P : F[X]} : Proper (ι P) ↔ P = 0 := by
  constructor
  · rintro ⟨N, D, h, e⟩
    by_contra hP
    have e' : P * D = N := RatFunc.algebraMap_injective F (by simpa using e)
    have hle : D.degree ≤ N.degree := by
      rw [← e', mul_comm]
      exact degree_le_mul_left _ hP
    exact absurd h (not_lt.2 hle)
  · rintro rfl
    simpa using proper_zero (F := F)

/-- The constant by which a fraction differs from a proper one is the quotient of its
numerator by its denominator. -/
theorem proper_sub_C_iff {Q A Ts N : F[X]} (hQ : Q = A * Ts + N)
    (hN : N.degree < Ts.degree) (c : F) :
    Proper (ι Q / ι Ts - RatFunc.C c) ↔ A = C c := by
  have hTs' : ι Ts ≠ 0 := RatFunc.algebraMap_ne_zero (ne_zero_of_degree_lt hN)
  have key : ι Q / ι Ts - RatFunc.C c = ι (A - C c) + ι N / ι Ts := by
    rw [hQ, map_add, map_mul, map_sub, RatFunc.algebraMap_C]
    field_simp
    ring
  have hNp : Proper (ι N / ι Ts) := proper_div hN
  rw [key]
  constructor
  · intro h
    have h' := h.sub hNp
    rw [add_sub_cancel_right] at h'
    exact sub_eq_zero.1 (proper_algebraMap_iff.1 h')
  · intro h
    rw [h, sub_self, map_zero, zero_add]
    exact hNp

end Proper

section Multiplicity

private theorem exists_pow_mul {p T : F[X]} (hp : Prime p) (hT : T ≠ 0) :
    ∃ (k : ℕ) (Q : F[X]), T = p ^ k * Q ∧ ¬ p ∣ Q :=
  ⟨_, (FiniteMultiplicity.of_prime_left hp hT).exists_eq_pow_mul_and_not_dvd⟩

private theorem le_of_pow_dvd_pow_mul {p Q : F[X]} (hp : Prime p) {j k : ℕ} (hQ : ¬ p ∣ Q)
    (h : p ^ j ∣ p ^ k * Q) : j ≤ k := by
  by_contra hlt
  have h1 : p ^ (k + 1) ∣ p ^ k * Q := (pow_dvd_pow p (by omega)).trans h
  rw [pow_succ] at h1
  exact hQ ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 h1)

private theorem dvd_of_forall_prime_pow_dvd {G W : F[X]} (hG : G ≠ 0)
    (h : ∀ p : F[X], Prime p → ∀ j : ℕ, p ^ j ∣ G → p ^ j ∣ W) : G ∣ W :=
  (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hG).2 fun p hp =>
    emultiplicity_le_emultiplicity_iff.2 (h p hp)

private theorem integral_mul_div_of_not_sq_dvd {p Q Ts : F[X]} (hp : Prime p) (hTs : Ts ≠ 0)
    (h : ¬ p ^ 2 ∣ Ts) : Integral p (ι p * (ι Q / ι Ts)) := by
  have hp' : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  by_cases hd : p ∣ Ts
  · obtain ⟨E, rfl⟩ := hd
    have hE : ¬ p ∣ E := fun ⟨c, hc⟩ => h ⟨c, by rw [hc]; ring⟩
    have hE0 : ι E ≠ 0 := RatFunc.algebraMap_ne_zero (right_ne_zero_of_mul hTs)
    exact ⟨Q, E, hE, by rw [map_mul]; field_simp⟩
  · have hTs' : ι Ts ≠ 0 := RatFunc.algebraMap_ne_zero hTs
    exact ⟨p * Q, Ts, hd, by rw [map_mul]; field_simp⟩

private theorem not_sq_dvd_of_gcd {p T G Ts : F[X]} (hp : Prime p) (hT : T ≠ 0)
    (hG : T = G * Ts) (hGdvd : ∀ k : ℕ, p ^ k ∣ T → p ^ (k - 1) ∣ G) : ¬ p ^ 2 ∣ Ts := by
  intro h
  obtain ⟨k, R, hTR, hR⟩ := exists_pow_mul hp hT
  have h1 : p ^ (k - 1) ∣ G := hGdvd k ⟨R, hTR⟩
  have h2 : p ^ (k - 1 + 2) ∣ p ^ k * R := by
    rw [← hTR, hG, pow_add]
    exact mul_dvd_mul h1 h
  have := le_of_pow_dvd_pow_mul hp hR h2
  omega

end Multiplicity

section Squarefree

variable [CharZero F]

private theorem not_dvd_derivative_self {p : F[X]} (hp : Prime p) : ¬ p ∣ derivative p := by
  intro h
  have h0 : derivative p = 0 :=
    eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hp.ne_zero)
  have hnd : p.natDegree = 0 := derivative_eq_zero.1 h0
  have hpos := degree_pos_of_irreducible hp.irreducible
  rw [degree_eq_natDegree hp.ne_zero, hnd] at hpos
  simp at hpos

private theorem natCast_succ_not_dvd {p : F[X]} (hp : Prime p) (k : ℕ) :
    ¬ p ∣ ((k + 1 : ℕ) : F[X]) := by
  intro h
  have hu : IsUnit ((k + 1 : ℕ) : F[X]) := by
    rw [← C_eq_natCast]
    exact isUnit_C.2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)))
  exact hp.not_isUnit (isUnit_of_dvd_unit h hu)

/-- In characteristic zero a prime dividing a polynomial exactly `k ≥ 1` times divides its
derivative fewer than `k` times. -/
theorem not_pow_dvd_derivative {p T : F[X]} (hp : Prime p) {k : ℕ} (hk : p ^ (k + 1) ∣ T)
    (hk' : ¬ p ^ (k + 2) ∣ T) : ¬ p ^ (k + 1) ∣ derivative T := by
  obtain ⟨Q, rfl⟩ := hk
  have hQ : ¬ p ∣ Q := fun ⟨c, hc⟩ => hk' ⟨c, by rw [hc]; ring⟩
  intro h
  have hd : derivative (p ^ (k + 1) * Q) =
      p ^ k * (((k + 1 : ℕ) : F[X]) * derivative p * Q + p * derivative Q) := by
    rw [derivative_mul, derivative_pow, C_eq_natCast, Nat.add_sub_cancel]
    ring
  rw [hd, pow_succ] at h
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 h
  have h3 : p ∣ ((k + 1 : ℕ) : F[X]) * derivative p * Q :=
    (dvd_add_left (dvd_mul_right p _)).1 h2
  rcases hp.dvd_or_dvd h3 with h4 | h4
  · rcases hp.dvd_or_dvd h4 with h5 | h5
    · exact natCast_succ_not_dvd hp k h5
    · exact not_dvd_derivative_self hp h5
  · exact hQ h4

private theorem pow_dvd_of_integral_mul {p T W : F[X]} (hp : Prime p) (hT : T ≠ 0)
    (hs : Integral p (ι p * (ι W / ι T))) {j : ℕ} (hjT : p ^ j ∣ T)
    (hjT' : p ^ j ∣ derivative T) : p ^ j ∣ W := by
  obtain ⟨k, R, hTR, hR⟩ := exists_pow_mul hp hT
  have hjk : j ≤ k := le_of_pow_dvd_pow_mul hp hR (by rw [← hTR]; exact hjT)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : p ^ (k' + 1) ∣ T := ⟨R, hTR⟩
  have h2 : ¬ p ^ (k' + 2) ∣ T := fun h => by
    have := le_of_pow_dvd_pow_mul hp hR (by rw [← hTR]; exact h)
    omega
  have h3 := not_pow_dvd_derivative hp h1 h2
  have hjk' : j ≤ k' := by
    by_contra hc
    exact h3 ((pow_dvd_pow p (by omega)).trans hjT')
  exact Integral.pow_dvd_of_mul hp hT hs ((pow_dvd_pow p (by omega)).trans h1)

/-- With `G` a greatest common divisor of `T` and its derivative: the fraction `W/T` has at
most simple poles exactly when `G` divides `W`. -/
theorem simple_div_iff {T G Ts a b : F[X]} (hT : T ≠ 0) (hG : T = G * Ts)
    (bez : a * T + b * derivative T = G) (hd : G ∣ derivative T) (W : F[X]) :
    Simple (ι W / ι T) ↔ G ∣ W := by
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hT (by simpa using hG)
  have hTs0 : Ts ≠ 0 := by
    rintro rfl
    exact hT (by simpa using hG)
  have hG' : ι G ≠ 0 := RatFunc.algebraMap_ne_zero hG0
  have hTs' : ι Ts ≠ 0 := RatFunc.algebraMap_ne_zero hTs0
  constructor
  · intro hs
    refine dvd_of_forall_prime_pow_dvd hG0 fun p hp j hj => ?_
    exact pow_dvd_of_integral_mul hp hT (hs p hp) (hj.trans ⟨Ts, hG⟩) (hj.trans hd)
  · rintro ⟨Q, rfl⟩
    have e : ι (G * Q) / ι T = ι Q / ι Ts := by
      rw [hG, map_mul, map_mul]
      field_simp
    rw [e]
    intro p hp
    refine integral_mul_div_of_not_sq_dvd hp hTs0 (not_sq_dvd_of_gcd hp hT hG fun k hk => ?_)
    rw [← bez]
    exact dvd_add (((pow_dvd_pow p (Nat.sub_le k 1)).trans hk).mul_left a)
      ((pow_sub_one_dvd_derivative_of_pow_dvd hk).mul_left b)

/-- With `G` a greatest common divisor of `T` and `X` times its derivative: the fraction
`W/T` has at most simple poles and no pole at `X` exactly when `G` divides `W`. -/
theorem simple_integral_div_iff {T G Ts a b : F[X]} (hT : T ≠ 0) (hG : T = G * Ts)
    (bez : a * T + b * (X * derivative T) = G) (hd : G ∣ X * derivative T) (W : F[X]) :
    (Simple (ι W / ι T) ∧ Integral X (ι W / ι T)) ↔ G ∣ W := by
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hT (by simpa using hG)
  have hTs0 : Ts ≠ 0 := by
    rintro rfl
    exact hT (by simpa using hG)
  have hG' : ι G ≠ 0 := RatFunc.algebraMap_ne_zero hG0
  have hTs' : ι Ts ≠ 0 := RatFunc.algebraMap_ne_zero hTs0
  constructor
  · rintro ⟨hs, hi⟩
    refine dvd_of_forall_prime_pow_dvd hG0 fun p hp j hj => ?_
    have hjT : p ^ j ∣ T := hj.trans ⟨Ts, hG⟩
    by_cases hpX : p ∣ X
    · exact Integral.pow_dvd hp hT (Integral.of_dvd hp prime_X hpX hi) hjT
    · exact pow_dvd_of_integral_mul hp hT (hs p hp) hjT
        (hp.pow_dvd_of_dvd_mul_left j hpX (hj.trans hd))
  · rintro ⟨Q, rfl⟩
    have e : ι (G * Q) / ι T = ι Q / ι Ts := by
      rw [hG, map_mul, map_mul]
      field_simp
    rw [e]
    refine ⟨fun p hp => integral_mul_div_of_not_sq_dvd hp hTs0
      (not_sq_dvd_of_gcd hp hT hG fun k hk => ?_), ?_⟩
    · rw [← bez]
      exact dvd_add (((pow_dvd_pow p (Nat.sub_le k 1)).trans hk).mul_left a)
        (((pow_sub_one_dvd_derivative_of_pow_dvd hk).mul_left X).mul_left b)
    · refine ⟨Q, Ts, fun hX => ?_, div_mul_cancel₀ _ hTs'⟩
      obtain ⟨k, R, hTR, hR⟩ := exists_pow_mul prime_X hT
      have hk : X ^ k ∣ T := ⟨R, hTR⟩
      have h1 : X ^ k ∣ X * derivative T := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp
        · have h := mul_dvd_mul_left X (pow_sub_one_dvd_derivative_of_pow_dvd hk)
          rwa [← pow_succ', Nat.sub_add_cancel hk0] at h
      have h2 : X ^ k ∣ G := by
        rw [← bez]
        exact dvd_add (hk.mul_left a) (h1.mul_left b)
      have h3 : X ^ (k + 1) ∣ X ^ k * R := by
        rw [← hTR, hG, pow_succ]
        exact mul_dvd_mul h2 hX
      have := le_of_pow_dvd_pow_mul prime_X hR h3
      omega

end Squarefree

section Derivation

variable (δ : Derivation ℤ F[X] F[X])

/-- A logarithmic derivative has at most simple poles. -/
theorem simple_logDeriv {P : F[X]} (hP : P ≠ 0) : Simple (ι (δ P) / ι P) := by
  intro p hp
  obtain ⟨k, Q, hPQ, hQ⟩ := exists_pow_mul hp hP
  have hp' : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hQ (dvd_zero p)
  have hQ' : ι Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ0
  have hkey : p * δ P = ((k : F[X]) * δ p * Q + p * δ Q) * p ^ k := by
    rw [hPQ, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul]
    cases k with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  refine ⟨(k : F[X]) * δ p * Q + p * δ Q, Q, hQ, ?_⟩
  have hP' : ι P = ι p ^ k * ι Q := by rw [hPQ, map_mul, map_pow]
  rw [← mul_div_assoc, ← map_mul, hkey, hP', map_mul, map_pow]
  field_simp

/-- When the derivative of `X` is a multiple of `X`, a logarithmic derivative has no pole at
`X`. -/
theorem integral_X_logDeriv {b P : F[X]} (hX : δ X = b * X) (hP : P ≠ 0) :
    Integral X (ι (δ P) / ι P) := by
  obtain ⟨k, Q, hPQ, hQ⟩ := exists_pow_mul prime_X hP
  have hX' : ι (X : F[X]) ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hQ (dvd_zero X)
  have hQ' : ι Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ0
  have hkey : δ P = ((k : F[X]) * b * Q + δ Q) * X ^ k := by
    rw [hPQ, Derivation.leibniz, Derivation.leibniz_pow, hX]
    simp only [smul_eq_mul, nsmul_eq_mul]
    cases k with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  refine ⟨(k : F[X]) * b * Q + δ Q, Q, hQ, ?_⟩
  have hP' : ι P = ι X ^ k * ι Q := by rw [hPQ, map_mul, map_pow]
  rw [hkey, hP', map_mul, map_pow]
  field_simp

/-- At a normal prime the derivative of a fraction with a pole has a multiple pole. -/
theorem not_dvd_of_simple_deriv [CharZero F] {p u d : F[X]} (hp : Prime p)
    (normal : ¬ p ∣ δ p) (hd : d ≠ 0) (cop : IsCoprime u d)
    (h : Integral p (ι p * (ι (δ u * d - u * δ d) / ι (d * d)))) : ¬ p ∣ d := by
  intro hpd
  obtain ⟨m, e, hde, he⟩ := exists_pow_mul hp hd
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · exact absurd (by simpa [hde] using hpd) he
    · exact ⟨k, rfl⟩
  have hu : ¬ p ∣ u := fun h => hp.not_isUnit (cop.isUnit_of_dvd' h hpd)
  obtain ⟨N, D, hD, eq⟩ := h
  have hd' : ι d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have eq' : p * (δ u * d - u * δ d) * D = N * (d * d) := by
    apply RatFunc.algebraMap_injective F
    simp only [map_mul] at eq ⊢
    rw [← eq]
    field_simp
  have hδd : δ d = p ^ (k + 1) * δ e + e * (((k + 1 : ℕ) : F[X]) * (p ^ k * δ p)) := by
    rw [hde, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  obtain ⟨M, hM⟩ : ∃ M, M = (δ u * e - u * δ e) * p - ((k + 1 : ℕ) : F[X]) * u * δ p * e :=
    ⟨_, rfl⟩
  have h1 : δ u * d - u * δ d = p ^ k * M := by
    rw [hδd, hde, hM]
    ring
  have h2 : p ^ (k + 1) * (M * D) = p ^ (k + 1) * (N * p ^ (k + 1) * e * e) := by
    have h := eq'
    rw [h1, hde] at h
    linear_combination h
  have h3 := mul_left_cancel₀ (pow_ne_zero (k + 1) hp.ne_zero) h2
  have h4 : p ∣ M * D := ⟨N * p ^ k * e * e, by rw [h3]; ring⟩
  have h5 : p ∣ M := (hp.dvd_or_dvd h4).resolve_right hD
  have h6 : p ∣ ((k + 1 : ℕ) : F[X]) * u * δ p * e := by
    have h : ((k + 1 : ℕ) : F[X]) * u * δ p * e = (δ u * e - u * δ e) * p - M := by
      rw [hM]
      ring
    rw [h]
    exact dvd_sub (dvd_mul_left p _) h5
  rcases hp.dvd_or_dvd h6 with h7 | h7
  · rcases hp.dvd_or_dvd h7 with h8 | h8
    · rcases hp.dvd_or_dvd h8 with h9 | h9
      · exact natCast_succ_not_dvd hp k h9
      · exact hu h9
    · exact normal h8
  · exact he h7

end Derivation

end SympyProofs.Calculus.Risch.SimplePole
