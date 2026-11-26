module

public import SympyProofs.Calculus.Antiderivative.Extension.Residue
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic.Ring

/-! Pairwise coprime divisors of a polynomial `D` whose degrees add up to the degree of `D`
account for every prime factor of `D`, and conversely when `D` is squarefree. The divisors
`gcd(A - c D′, D)` for distinct constants `c` are pairwise coprime when the prime factors of
`D` are normal. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension.Residue

open Polynomial

variable {F : Type*} [Field F]

/-- Pairwise coprime divisors of `D` whose degrees add up to the degree of `D`: every prime
factor of `D` divides one of them. -/
theorem exists_dvd_of_degree_sum {D : F[X]} (hD : D ≠ 0) {ι : Type*} (s : Finset ι)
    (G : ι → F[X]) (dvd : ∀ i ∈ s, G i ∣ D)
    (cop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (G i) (G j))
    (deg : ∑ i ∈ s, (G i).natDegree = D.natDegree) {p : F[X]} (hp : Prime p) (hpD : p ∣ D) :
    ∃ i ∈ s, p ∣ G i := by
  have ne : ∀ i ∈ s, G i ≠ 0 := fun i hi z => hD (zero_dvd_iff.mp (z ▸ dvd i hi))
  have pd : ∏ i ∈ s, G i ∣ D :=
    Finset.prod_dvd_of_coprime (fun i hi j hj hij => cop i hi j hj hij) dvd
  obtain ⟨Q, hQ⟩ := pd
  have Qn : Q ≠ 0 := fun z => hD (by rw [hQ, z, mul_zero])
  have pn : ∏ i ∈ s, G i ≠ 0 := Finset.prod_ne_zero_iff.mpr ne
  have dq : Q.natDegree = 0 := by
    have := congrArg natDegree hQ
    rw [natDegree_mul pn Qn, natDegree_prod _ _ ne, deg] at this
    omega
  have unit : IsUnit Q := by
    rw [eq_C_of_natDegree_eq_zero dq]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun z => Qn (by
      rw [eq_C_of_natDegree_eq_zero dq, z, C_0]))
  have : p ∣ ∏ i ∈ s, G i := by
    rw [hQ] at hpD
    exact (hp.dvd_or_dvd hpD).resolve_right fun h => hp.not_isUnit (isUnit_of_dvd_unit h unit)
  exact (Prime.dvd_finsetProd_iff hp G).mp this

/-- Pairwise coprime divisors of a squarefree `D` such that every prime factor of `D`
divides one of them: their degrees add up to the degree of `D`. -/
theorem degree_sum_of_cover {D : F[X]} (hs : Squarefree D) {ι : Type*} (s : Finset ι)
    (G : ι → F[X]) (dvd : ∀ i ∈ s, G i ∣ D)
    (cop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (G i) (G j))
    (cover : ∀ p : F[X], Prime p → p ∣ D → ∃ i ∈ s, p ∣ G i) :
    ∑ i ∈ s, (G i).natDegree = D.natDegree := by
  have hD : D ≠ 0 := hs.ne_zero
  have ne : ∀ i ∈ s, G i ≠ 0 := fun i hi z => hD (zero_dvd_iff.mp (z ▸ dvd i hi))
  have pd : ∏ i ∈ s, G i ∣ D :=
    Finset.prod_dvd_of_coprime (fun i hi j hj hij => cop i hi j hj hij) dvd
  have dp : D ∣ ∏ i ∈ s, G i := dvd_of_squarefree hs fun p hp hpD => by
    obtain ⟨i, hi, hpi⟩ := cover p hp hpD
    exact hpi.trans (Finset.dvd_prod_of_mem G hi)
  have pn : ∏ i ∈ s, G i ≠ 0 := Finset.prod_ne_zero_iff.mpr ne
  have e := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (associated_of_dvd_dvd pd dp))
  rw [← e, natDegree_prod _ _ ne]

/-- The greatest common divisors of `D` with `A - c D′` for two distinct constants are
coprime, when the prime factors of `D` are normal. -/
theorem isCoprime_of_ne (δ : Derivation ℤ F[X] F[X]) {D A G₁ G₂ : F[X]} (hs : Squarefree D)
    (normal : ∀ p : F[X], Prime p → p ∣ D → ¬ p ∣ δ p) {c₁ c₂ : F} (hc : c₁ ≠ c₂)
    (d₁ : G₁ ∣ D) (r₁ : G₁ ∣ A - C c₁ * δ D) (r₂ : G₂ ∣ A - C c₂ * δ D) :
    IsCoprime G₁ G₂ := by
  have hD : D ≠ 0 := hs.ne_zero
  have n₁ : G₁ ≠ 0 := fun z => hD (zero_dvd_iff.mp (z ▸ d₁))
  apply isCoprime_of_prime_dvd (fun h => n₁ h.1)
  intro p hp h1 h2
  have hpD : p ∣ D := h1.trans d₁
  have diff : p ∣ C (c₂ - c₁) * δ D := by
    have := dvd_sub (h1.trans r₁) (h2.trans r₂)
    have e : A - C c₁ * δ D - (A - C c₂ * δ D) = C (c₂ - c₁) * δ D := by
      rw [C_sub]
      ring
    rwa [e] at this
  have unit : IsUnit (C (c₂ - c₁) : F[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hc)))
  have : p ∣ δ D := (hp.dvd_or_dvd diff).resolve_left fun h =>
    hp.not_isUnit (isUnit_of_dvd_unit h unit)
  exact not_dvd_deriv δ hs hp hpD (normal p hp hpD) this

end SympyProofs.Calculus.Antiderivative.Extension.Residue
