module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The logarithmic part of a fraction `A/Ds` with squarefree denominator and normal prime
factors. When at every prime factor of `Ds` the numerator is congruent to a constant from a
given list times the derivative of `Ds`, subtracting the logarithmic derivatives of the
corresponding greatest common divisors, with those constants as coefficients, leaves a
polynomial. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension.Residue

open Polynomial

variable {F : Type*} [Field F]

/-- A squarefree polynomial divides whatever all of its prime factors divide. -/
theorem dvd_of_squarefree {Ds M : F[X]} (hs : Squarefree Ds)
    (h : ∀ p : F[X], Prime p → p ∣ Ds → p ∣ M) : Ds ∣ M := by
  refine (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hs.ne_zero).2 fun p hp =>
    emultiplicity_le_emultiplicity_iff.2 fun k hk => ?_
  rcases k with _ | _ | k
  · simp
  · rw [pow_one] at hk ⊢
    exact h p hp hk
  · exfalso
    have h2 : p * p ∣ Ds := by
      rw [← pow_two]
      exact (pow_dvd_pow p (by omega)).trans hk
    exact hp.not_isUnit (hs p h2)

/-- A normal prime factor of a squarefree polynomial does not divide its derivative. -/
theorem not_dvd_deriv (δ : Derivation ℤ F[X] F[X]) {Ds p : F[X]} (hs : Squarefree Ds)
    (hp : Prime p) (hpd : p ∣ Ds) (normal : ¬ p ∣ δ p) : ¬ p ∣ δ Ds := by
  obtain ⟨E, rfl⟩ := hpd
  have hE : ¬ p ∣ E := fun ⟨c, hc⟩ => hp.not_isUnit (hs p ⟨c, by rw [hc]; ring⟩)
  intro h
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  have h2 : p ∣ E * δ p := (dvd_add_right (dvd_mul_right p _)).1 h
  rcases hp.dvd_or_dvd h2 with h3 | h3
  exacts [hE h3, normal h3]

/-- `G c` collects the prime factors of `Ds` with residue `c`, and `H c` is the cofactor.
If every prime factor has a residue in the list, then `Ds` divides the numerator left after
subtracting the logarithmic derivatives. -/
theorem residue_sum_dvd (δ : Derivation ℤ F[X] F[X]) {Ds A : F[X]} (hs : Squarefree Ds)
    (normal : ∀ p : F[X], Prime p → p ∣ Ds → ¬ p ∣ δ p) (cs : List F) (nodup : cs.Nodup)
    (G H : F → F[X]) (hGH : ∀ c ∈ cs, G c * H c = Ds)
    (hG : ∀ c ∈ cs, ∀ p : F[X], Prime p → p ∣ G c → p ∣ A - C c * δ Ds)
    (hG' : ∀ c ∈ cs, ∀ p : F[X], Prime p → p ∣ Ds → p ∣ A - C c * δ Ds → p ∣ G c)
    (res : ∀ p : F[X], Prime p → p ∣ Ds → ∃ c ∈ cs, p ∣ A - C c * δ Ds) :
    Ds ∣ A - (cs.map fun c => C c * δ (G c) * H c).sum := by
  classical
  refine dvd_of_squarefree hs fun p hp hpDs => ?_
  obtain ⟨c₀, hc₀, hres⟩ := res p hp hpDs
  have hpG : p ∣ G c₀ := hG' c₀ hc₀ p hp hpDs hres
  have hnd := not_dvd_deriv δ hs hp hpDs (normal p hp hpDs)
  have hother : ∀ c ∈ cs.erase c₀, p ∣ C c * δ (G c) * H c := by
    intro c hc
    obtain ⟨hcne, hcm⟩ := nodup.mem_erase_iff.1 hc
    have hnG : ¬ p ∣ G c := by
      intro hpc
      have h1 := hG c hcm p hp hpc
      have h2 : p ∣ C (c - c₀) * δ Ds := by
        have h3 := dvd_sub hres h1
        have e : A - C c₀ * δ Ds - (A - C c * δ Ds) = C (c - c₀) * δ Ds := by
          rw [C_sub]
          ring
        rwa [e] at h3
      have hu : IsUnit (C (c - c₀) : F[X]) :=
        isUnit_C.2 (IsUnit.mk0 _ (sub_ne_zero.2 hcne))
      exact hnd (hu.dvd_mul_left.1 h2)
    have h4 : p ∣ G c * H c := by
      rw [hGH c hcm]
      exact hpDs
    exact ((hp.dvd_or_dvd h4).resolve_left hnG).mul_left _
  have hc0 : p ∣ A - C c₀ * δ (G c₀) * H c₀ := by
    have hD : δ Ds = G c₀ * δ (H c₀) + H c₀ * δ (G c₀) := by
      rw [← hGH c₀ hc₀, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have e : A - C c₀ * δ (G c₀) * H c₀ = (A - C c₀ * δ Ds) + G c₀ * (C c₀ * δ (H c₀)) := by
      rw [hD]
      ring
    rw [e]
    exact dvd_add hres (hpG.mul_right _)
  have hsum : (cs.map fun c => C c * δ (G c) * H c).sum =
      C c₀ * δ (G c₀) * H c₀ + ((cs.erase c₀).map fun c => C c * δ (G c) * H c).sum := by
    rw [← List.sum_cons, ← List.map_cons (f := fun c => C c * δ (G c) * H c)]
    exact ((List.perm_cons_erase hc₀).map _).sum_eq
  rw [hsum, ← sub_sub]
  refine dvd_sub hc0 (List.dvd_sum fun x hx => ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  exact hother c hc

end SympyProofs.Calculus.Antiderivative.Extension.Residue
