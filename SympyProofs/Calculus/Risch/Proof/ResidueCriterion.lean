module

public import SympyProofs.Calculus.Risch.Algebra.SimplePole
public import SympyProofs.Calculus.Risch.Spec.Elementary
public import SympyProofs.Calculus.Risch.Proof.Rel
public import SympyProofs.Calculus.Risch.Proof.Pole
public import SympyProofs.Calculus.Risch.Proof.Constants
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The residue criterion (Risch 1969, p. 181): if `A/Ds + L` has an elementary integral
over the field of a tower step, where `Ds` is squarefree with normal prime factors and `L`
has no pole at them, then at each prime factor `p` of `Ds` the numerator `A` is congruent to
a constant multiple of the derivative of `Ds`. The constant is the residue at `p`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial SimplePole

noncomputable local instance intAlgebraResidueCriterion {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

namespace SimplePole

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- A finite sum of rational functions without a pole at `p` has no pole at `p`. -/
theorem integral_finset_sum {p : F[X]} (hp : Prime p) {α : Type*} (s : Finset α)
    (f : α → RatFunc F) (h : ∀ i ∈ s, Integral p (f i)) : Integral p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    simpa using integral_algebraMap hp (0 : F[X])
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add hp
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Near a prime, the logarithmic derivative of a polynomial is the order at the prime times
the logarithmic derivative of the prime. -/
theorem local_logDeriv_poly (δ : Derivation ℤ F[X] F[X]) {p P : F[X]} (hp : Prime p)
    (hP : P ≠ 0) :
    ∃ k : ℕ, Integral p (ι (δ P) / ι P - (k : RatFunc F) * (ι (δ p) / ι p)) := by
  obtain ⟨Q, hQ, hPQ⟩ := (FiniteMultiplicity.of_prime_left hp hP).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p P = k at hQ
  have hp0 : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have Q0 : Q ≠ 0 := fun z => hP (by rw [hQ, z, mul_zero])
  have hQ0 : ι Q ≠ 0 := RatFunc.algebraMap_ne_zero Q0
  refine ⟨k, δ Q, Q, hPQ, ?_⟩
  rw [hQ]
  cases k with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, sub_zero]
    field_simp
  | succ k =>
    simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel, map_add, map_mul, map_pow, map_natCast]
    rw [pow_succ]
    push_cast
    field_simp
    ring

/-- A simple pole with residue `r` relative to the logarithmic derivative of the prime makes
the numerator congruent to `r` times the derivative of the denominator. -/
theorem dvd_of_integral_residue (δ : Derivation ℤ F[X] F[X]) {p A E : F[X]} (hp : Prime p)
    (hE : ¬ p ∣ E) (r : F)
    (h : Integral p (ι A / ι (p * E) - RatFunc.C r * (ι (δ p) / ι p))) :
    p ∣ A - C r * δ (p * E) := by
  have hp0 : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have E0 : E ≠ 0 := fun z => hE (z ▸ dvd_zero p)
  have hE0 : ι E ≠ 0 := RatFunc.algebraMap_ne_zero E0
  have e : ι A / ι (p * E) - RatFunc.C r * (ι (δ p) / ι p) =
      ι (A - C r * δ p * E) / ι (p * E) := by
    rw [map_sub, map_mul, map_mul, map_mul, RatFunc.algebraMap_C]
    field_simp
  rw [e] at h
  have d1 : p ^ 1 ∣ A - C r * δ p * E :=
    h.pow_dvd hp (mul_ne_zero hp.ne_zero E0) (by rw [pow_one]; exact dvd_mul_right p E)
  rw [pow_one] at d1
  have split : A - C r * δ (p * E) = (A - C r * δ p * E) - p * (C r * δ E) := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  rw [split]
  exact dvd_sub d1 (dvd_mul_right _ _)

end SimplePole

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-- A logarithmic derivative in the field of a tower step has at most simple poles. -/
theorem Tower.simple_logDeriv (t : Tower (n+1)) {u : K k (n+1)} (hu : u ≠ 0) :
    SimplePole.Simple (t.der k u / u) := by
  have h := Tower.rel_logDeriv t hu
  cases t with
  | prim low b => exact (Tower.rel_prim.mp h).1
  | exp low w => exact (Tower.rel_exp.mp h).1

/-- Near a prime, a logarithmic derivative is an integer times the logarithmic derivative of
the prime. -/
theorem Tower.local_logDeriv (t : Tower (n+1)) {p : (K k n)[X]} (hp : Prime p)
    {u : K k (n+1)} (hu : u ≠ 0) :
    ∃ e : ℤ, SimplePole.Integral p (t.der k u / u -
      (e : RatFunc (K k n)) * (ι (Tower.polyDer k t p) / ι p)) := by
  obtain ⟨N, d, hN, hd, rfl⟩ : ∃ N d : (K k n)[X], N ≠ 0 ∧ d ≠ 0 ∧ u = ι N / ι d :=
    ⟨_, _, RatFunc.num_ne_zero hu, RatFunc.denom_ne_zero u, (RatFunc.num_div_denom u).symm⟩
  obtain ⟨i, hi⟩ := local_logDeriv_poly (Tower.polyDer k t) hp hN
  obtain ⟨j, hj⟩ := local_logDeriv_poly (Tower.polyDer k t) hp hd
  refine ⟨(i : ℤ) - (j : ℤ), ?_⟩
  rw [logDeriv_div (RatFunc.algebraMap_ne_zero hN) (RatFunc.algebraMap_ne_zero hd),
    Tower.der_algebraMap, Tower.der_algebraMap]
  have := hi.sub hp hj
  convert this using 1
  push_cast
  ring

/-- The residue criterion: when `A/Ds + L` has an elementary integral, with `Ds` squarefree,
its prime factors normal and `L` without a pole at them, each prime factor of `Ds` divides
`A - r Ds′` for some constant `r`. -/
theorem Tower.residue_necessary (t : Tower (n+1)) {A Ds : (K k n)[X]}
    {L : RatFunc (K k n)} (hs : Squarefree Ds)
    (normal : ∀ p : (K k n)[X], Prime p → p ∣ Ds → ¬ p ∣ Tower.polyDer k t p)
    (hL : ∀ p : (K k n)[X], Prime p → p ∣ Ds → SimplePole.Integral p L)
    (form : t.Elementary k (ι A / ι Ds + L)) :
    ∀ p : (K k n)[X], Prime p → p ∣ Ds →
      ∃ r : k, p ∣ A - C (constHom k n r) * Tower.polyDer k t Ds := by
  intro p hp hpd
  obtain ⟨κ, _, c, u, w, he⟩ := form
  have nrm := normal p hp hpd
  have iL := hL p hp hpd
  obtain ⟨E, rfl⟩ := hpd
  have hE : ¬ p ∣ E := fun h => hp.not_isUnit (hs p (mul_dvd_mul_left p h))
  have hp0 : ι p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have E0 : E ≠ 0 := fun z => hE (z ▸ dvd_zero p)
  have hE0 : ι E ≠ 0 := RatFunc.algebraMap_ne_zero E0
  have cint (i : κ) : Integral p (constHom k (n+1) (c i)) := by
    rw [constHom_succ, ← RatFunc.algebraMap_C]
    exact integral_algebraMap hp _
  -- the derivative of `w` has at most a simple pole at `p`
  have s1 : Integral p (ι p * (ι A / ι (p * E))) := ⟨A, E, hE, by
    rw [map_mul]
    field_simp⟩
  have s3 (i : κ) : Integral p (ι p * (constHom k (n+1) (c i) * (t.der k (u i) / u i))) := by
    by_cases hu : u i = 0
    · rw [hu, map_zero, zero_div, mul_zero, mul_zero]
      simpa using integral_algebraMap hp (0 : (K k n)[X])
    · have := (cint i).mul hp (Tower.simple_logDeriv t hu p hp)
      rwa [mul_left_comm] at this
  have sw : Integral p (ι p * t.der k w) := by
    have e : ι p * t.der k w = ι p * (ι A / ι (p * E)) + ι p * L -
        ∑ i, ι p * (constHom k (n+1) (c i) * (t.der k (u i) / u i)) := by
      rw [← Finset.mul_sum]
      linear_combination (-(ι p)) * he
    rw [e]
    exact ((s1.add hp ((integral_algebraMap hp p).mul hp iL)).sub hp
      (integral_finset_sum hp _ _ fun i _ => s3 i))
  obtain ⟨N, d, hd, cop, rfl⟩ : ∃ N d : (K k n)[X], d ≠ 0 ∧ IsCoprime N d ∧
      w = ι N / ι d :=
    ⟨_, _, RatFunc.denom_ne_zero w, RatFunc.isCoprime_num_denom w,
      (RatFunc.num_div_denom w).symm⟩
  rw [Pole.der_div t N hd] at sw
  have npd : ¬ p ∣ d := not_dvd_of_simple_deriv (Tower.polyDer k t) hp nrm hd cop sw
  have iw : Integral p (t.der k (ι N / ι d)) := by
    rw [Pole.der_div t N hd]
    refine ⟨Tower.polyDer k t N * d - N * Tower.polyDer k t d, d * d,
      fun h => (hp.dvd_mul.mp h).elim npd npd, ?_⟩
    have hd0 : ι (d * d) ≠ 0 := RatFunc.algebraMap_ne_zero (mul_ne_zero hd hd)
    rw [div_mul_cancel₀ _ hd0]
  -- the local form of each logarithmic derivative
  have loc (i : κ) : ∃ e : ℤ, Integral p (t.der k (u i) / u i -
      (e : RatFunc (K k n)) * (ι (Tower.polyDer k t p) / ι p)) := by
    by_cases hu : u i = 0
    · refine ⟨0, ?_⟩
      rw [hu, map_zero, zero_div, Int.cast_zero, zero_mul, sub_zero]
      simpa using integral_algebraMap hp (0 : (K k n)[X])
    · exact Tower.local_logDeriv t hp hu
  choose e hloc using loc
  refine ⟨∑ i, c i * (e i : k), ?_⟩
  apply dvd_of_integral_residue (Tower.polyDer k t) hp hE
  have hC : RatFunc.C (constHom k n (∑ i, c i * (e i : k))) =
      ∑ i, constHom k (n+1) (c i) * (e i : RatFunc (K k n)) := by
    rw [← constHom_succ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast]
  have key : ι A / ι (p * E) - RatFunc.C (constHom k n (∑ i, c i * (e i : k))) *
      (ι (Tower.polyDer k t p) / ι p) =
      ∑ i, constHom k (n+1) (c i) * (t.der k (u i) / u i -
        (e i : RatFunc (K k n)) * (ι (Tower.polyDer k t p) / ι p)) +
        t.der k (ι N / ι d) - L := by
    rw [hC, Finset.sum_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc]
    linear_combination he
  rw [key]
  exact ((integral_finset_sum hp _ _ fun i _ => (cint i).mul hp (hloc i)).add hp iw).sub hp iL

end SympyProofs.Calculus.Risch
