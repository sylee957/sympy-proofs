module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The algebra behind Hermite reduction in the form that uses greatest common divisors
only (Mack's linear version): for a fraction `A/(Ds * Dm)` in which `Ds` is squarefree with
normal prime factors and every prime factor of `Dm` divides `Ds`, one step subtracts the
derivative of `B/Dm` and lowers the multiplicity of every prime factor of `Dm` by one. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension.Hermite

open Polynomial

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- One reduction step, as an identity of rational functions. The first term on the right is
the derivative of `B/Dm` by the quotient rule. -/
theorem step_identity (δ : Derivation ℤ F[X] F[X]) {A B C Dm Ds Dm2 Dms K E : F[X]}
    (hDm : Dm ≠ 0) (hDs : Ds ≠ 0) (h1 : Dm = Dm2 * Dms) (h2 : Ds = Dms * K)
    (hE : E * Dm = -(Ds * δ Dm)) (hB : B * E + C * Dms = A) :
    ι A / ι (Ds * Dm) =
      ι (δ B * Dm - B * δ Dm) / ι (Dm * Dm) + ι (C - δ B * K) / ι (Ds * Dm2) := by
  subst h1 h2
  have hDm2 : Dm2 ≠ 0 := left_ne_zero_of_mul hDm
  have hDms : Dms ≠ 0 := right_ne_zero_of_mul hDm
  have hK : K ≠ 0 := right_ne_zero_of_mul hDs
  have hDm2' : ι Dm2 ≠ 0 := RatFunc.algebraMap_ne_zero hDm2
  have hDms' : ι Dms ≠ 0 := RatFunc.algebraMap_ne_zero hDms
  have hK' : ι K ≠ 0 := RatFunc.algebraMap_ne_zero hK
  have e1 := congrArg ι hE
  have e2 := congrArg ι hB
  simp only [map_mul, map_add, map_sub, map_neg] at e1 e2 ⊢
  have n1 : ι Dms * ι K * (ι Dm2 * ι Dms) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hDms' hK') (mul_ne_zero hDm2' hDms')
  have n2 : ι Dm2 * ι Dms * (ι Dm2 * ι Dms) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hDm2' hDms') (mul_ne_zero hDm2' hDms')
  have n3 : ι Dms * ι K * ι Dm2 ≠ 0 := mul_ne_zero (mul_ne_zero hDms' hK') hDm2'
  rw [div_add_div _ _ n2 n3, div_eq_div_iff n1 (mul_ne_zero n2 n3), ← e2]
  linear_combination (ι B * (ι Dms * ι K) * ι Dm2 * (ι Dm2 * ι Dms)) * e1

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

/-- The derivation of a product with a prime power, with the power factored out. -/
private theorem derivation_pow_succ_mul (δ : Derivation ℤ F[X] F[X]) (p Q : F[X]) (j : ℕ) :
    δ (p ^ (j + 1) * Q) = p ^ j * (((j + 1 : ℕ) : F[X]) * δ p * Q + p * δ Q) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  ring

end Multiplicity

/-- The quotient of a polynomial by a greatest common divisor with its derivative is
squarefree. -/
theorem squarefree_of_gcd {D G Ds a b : F[X]} (hD : D ≠ 0) (hG : D = G * Ds)
    (bez : a * D + b * derivative D = G) : Squarefree Ds := by
  have hDs0 : Ds ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hG)
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hDs0]
  intro p hp
  rw [← pow_two]
  refine not_sq_dvd_of_gcd hp.prime hD hG fun k hk => ?_
  rw [← bez]
  exact dvd_add (((pow_dvd_pow p (Nat.sub_le k 1)).trans hk).mul_left a)
    ((pow_sub_one_dvd_derivative_of_pow_dvd hk).mul_left b)

/-- The squarefree part of `Dm` divides `Ds`. -/
theorem step_dvd_radical {Dm Ds G2 Dms a b : F[X]}
    (rad : ∀ p : F[X], Prime p → p ∣ Dm → p ∣ Ds) (hDm : Dm ≠ 0) (hG : Dm = G2 * Dms)
    (bez : a * Dm + b * derivative Dm = G2) : Dms ∣ Ds := by
  have hsq : Squarefree Dms := squarefree_of_gcd hDm hG bez
  have hDms0 : Dms ≠ 0 := by
    rintro rfl
    exact hDm (by simpa using hG)
  refine dvd_of_forall_prime_pow_dvd hDms0 fun p hp j hj => ?_
  rcases j with _ | _ | j
  · simp
  · rw [pow_one] at hj ⊢
    exact rad p hp (hG ▸ hj.mul_left G2)
  · exfalso
    have h2 : p * p ∣ Dms := by
      rw [← pow_two]
      exact (pow_dvd_pow p (by omega)).trans hj
    exact hp.not_isUnit (hsq p h2)

/-- The quotient defining the cofactor `E` is exact. -/
theorem step_dvd (δ : Derivation ℤ F[X] F[X]) {Dm Ds : F[X]}
    (rad : ∀ p : F[X], Prime p → p ∣ Dm → p ∣ Ds) (hDm : Dm ≠ 0) : Dm ∣ Ds * δ Dm := by
  refine dvd_of_forall_prime_pow_dvd hDm fun p hp j hj => ?_
  rcases j with _ | j
  · simp
  · have hpDs : p ∣ Ds := rad p hp ((dvd_pow_self p (Nat.succ_ne_zero j)).trans hj)
    obtain ⟨Q, rfl⟩ := hj
    rw [derivation_pow_succ_mul, pow_succ, mul_comm (p ^ j) p]
    exact mul_dvd_mul hpDs (dvd_mul_right _ _)

section CharZero

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
private theorem not_pow_dvd_derivative {p T : F[X]} (hp : Prime p) {k : ℕ}
    (hk : p ^ (k + 1) ∣ T) (hk' : ¬ p ^ (k + 2) ∣ T) : ¬ p ^ (k + 1) ∣ derivative T := by
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

/-- Every prime factor of a polynomial divides its quotient by a greatest common divisor
with its derivative. -/
theorem prime_dvd_of_gcd {D G Ds : F[X]} (hD : D ≠ 0) (hG : D = G * Ds)
    (hd : G ∣ derivative D) {p : F[X]} (hp : Prime p) (h : p ∣ D) : p ∣ Ds := by
  by_contra hnd
  obtain ⟨k, R, hDR, hR⟩ := exists_pow_mul hp hD
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with _ | k
    · exact absurd (by simpa [hDR] using h) hR
    · exact ⟨k, rfl⟩
  have h1 : p ^ (k' + 1) ∣ D := ⟨R, hDR⟩
  have h2 : ¬ p ^ (k' + 2) ∣ D := fun h => by
    have := le_of_pow_dvd_pow_mul hp hR (by rw [← hDR]; exact h)
    omega
  have h3 : p ^ (k' + 1) ∣ G := hp.pow_dvd_of_dvd_mul_right (k' + 1) hnd (hG ▸ h1)
  exact not_pow_dvd_derivative hp h1 h2 (h3.trans hd)

/-- The cofactor `E` is coprime to the squarefree part of `Dm`, when the prime factors of
`Ds` are normal. -/
theorem step_coprime (δ : Derivation ℤ F[X] F[X]) {Dm Ds G2 Dms E : F[X]}
    (hs : Squarefree Ds) (normal : ∀ p : F[X], Prime p → p ∣ Ds → ¬ p ∣ δ p)
    (rad : ∀ p : F[X], Prime p → p ∣ Dm → p ∣ Ds) (hDm : Dm ≠ 0) (hG : Dm = G2 * Dms)
    (hE : E * Dm = -(Ds * δ Dm)) : IsCoprime E Dms := by
  have hDms0 : Dms ≠ 0 := by
    rintro rfl
    exact hDm (by simpa using hG)
  refine isCoprime_of_prime_dvd (fun h => hDms0 h.2) fun p hp hpE hpDms => ?_
  have hpDm : p ∣ Dm := hG ▸ hpDms.mul_left G2
  have hpDs : p ∣ Ds := rad p hp hpDm
  obtain ⟨k, Q, hDQ, hQ⟩ := exists_pow_mul hp hDm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | k
    · exact absurd (by simpa [hDQ] using hpDm) hQ
    · exact ⟨k, rfl⟩
  have hnorm : ¬ p ∣ δ p := normal p hp hpDs
  obtain ⟨S, hS⟩ := hpDs
  have hS' : ¬ p ∣ S := fun ⟨c, hc⟩ =>
    hp.not_isUnit (hs p ⟨c, by rw [hS, hc]; ring⟩)
  obtain ⟨M, hM⟩ : ∃ M, M = ((j + 1 : ℕ) : F[X]) * δ p * Q + p * δ Q := ⟨_, rfl⟩
  have hM' : ¬ p ∣ M := by
    intro h
    rw [hM] at h
    have h3 : p ∣ ((j + 1 : ℕ) : F[X]) * δ p * Q := (dvd_add_left (dvd_mul_right p _)).1 h
    rcases hp.dvd_or_dvd h3 with h4 | h4
    · rcases hp.dvd_or_dvd h4 with h5 | h5
      · exact natCast_succ_not_dvd hp j h5
      · exact hnorm h5
    · exact hQ h4
  have hδ : δ Dm = p ^ j * M := by rw [hDQ, hM, derivation_pow_succ_mul]
  have h2 : p ^ (j + 1) * (E * Q) = p ^ (j + 1) * (-(S * M)) := by
    have h := hE
    rw [hδ, hS, hDQ] at h
    linear_combination h
  have h3 := mul_left_cancel₀ (pow_ne_zero (j + 1) hp.ne_zero) h2
  have h4 : p ∣ S * M := by
    rw [← dvd_neg, ← h3]
    exact hpE.mul_right Q
  exact (hp.dvd_or_dvd h4).elim hS' hM'

/-- A greatest common divisor with the derivative has smaller degree. -/
theorem step_degree {Dm G2 : F[X]} (hdeg : 0 < Dm.natDegree) (hd : G2 ∣ derivative Dm) :
    G2.natDegree < Dm.natDegree := by
  have hne : derivative Dm ≠ 0 := fun h => by
    have := derivative_eq_zero.1 h
    omega
  exact (natDegree_le_of_dvd hd hne).trans_lt (natDegree_derivative_lt hdeg.ne')

end CharZero

end SympyProofs.Calculus.Antiderivative.Extension.Hermite
