module

public import SympyProofs.Gosper.ShiftlessDecomposition.Primitives

/-! Degree decreases used by the recursive polynomial computations. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

theorem Primitives.Valid.gcd_monic {ops : Primitives K} (hops : ops.Valid)
    (p q : Polynomial K) (hp : p ≠ 0) : (ops.gcd p q).Monic := by
  rw [hops.gcd_eq, ← normalize_gcd]
  exact monic_normalize (fun h => hp ((gcd_eq_zero_iff p q).mp h).1)

theorem Primitives.Valid.squarefreePart_monic {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p.Monic) : (ops.squarefreePart p).Monic := by
  have hg := hops.gcd_monic p (ops.derivative p) hp.ne_zero
  exact hg.of_mul_monic_left
    ((hops.refinement_reconstruct p (ops.derivative p) hp.ne_zero).1.symm ▸ hp)

theorem Primitives.Valid.squarefree_next_eq_gcd {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p ≠ 0) :
    p / ops.squarefreePart p = ops.gcd p (ops.derivative p) := by
  obtain ⟨hs, he⟩ := hops.squarefreeStep_reconstruct p hp
  have hg := (hops.refinement_reconstruct p (ops.derivative p) hp).1
  change ops.gcd p (ops.derivative p) * ops.squarefreePart p = p at hg
  apply mul_left_cancel₀ hs
  rw [he, mul_comm, hg]

theorem Primitives.Valid.squarefree_next_monic {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p.Monic) : (p / ops.squarefreePart p).Monic := by
  rw [hops.squarefree_next_eq_gcd hp.ne_zero]
  exact hops.gcd_monic _ _ hp.ne_zero

/-- Cancel the common derivative factors from an exact divisibility relation. -/
theorem Primitives.Valid.squarefreePart_dvd_of_dvd_derivative_mul
    {ops : Primitives K} (hops : ops.Valid) {p q : Polynomial K} (hp : p ≠ 0)
    (hd : p ∣ p.derivative * q) : ops.squarefreePart p ∣ q := by
  let g := ops.gcd p (ops.derivative p)
  have hg : g ≠ 0 := (hops.gcd_monic p (ops.derivative p) hp).ne_zero
  have he : g * ops.squarefreePart p = p :=
    (hops.refinement_reconstruct p (ops.derivative p) hp).1
  have hd' : g * (p.derivative / g) = p.derivative := by
    simpa only [g, hops.derivative_eq] using
      (hops.refinement_reconstruct p (ops.derivative p) hp).2
  have hc : IsCoprime (ops.squarefreePart p) (p.derivative / g) := by
    simp only [Primitives.squarefreePart, g, hops.derivative_eq, hops.gcd_eq]
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (by simpa only [g, hops.derivative_eq, hops.gcd_eq] using hg)
  apply hc.dvd_of_dvd_mul_left
  apply (mul_dvd_mul_iff_left hg).mp
  rwa [← mul_assoc, he, hd']

/-- The remaining polynomial has no factors outside the layer just extracted. -/
theorem Primitives.Valid.squarefree_next_dvd_derivative_mul
    {ops : Primitives K} (hops : ops.Valid) {p : Polynomial K} (hp : p ≠ 0) :
    let q := p / ops.squarefreePart p
    q ∣ q.derivative * ops.squarefreePart p := by
  let q := p / ops.squarefreePart p
  have he : q * ops.squarefreePart p = p := by
    rw [mul_comm]
    exact (hops.squarefreeStep_reconstruct p hp).2
  have hd : q ∣ p.derivative := by
    dsimp only [q]
    rw [hops.squarefree_next_eq_gcd hp, hops.gcd_eq, hops.derivative_eq]
    exact gcd_dvd_right p p.derivative
  rw [← he, derivative_mul] at hd
  simpa only [add_sub_cancel_right] using
    dvd_sub hd (dvd_mul_right q (ops.squarefreePart p).derivative)

theorem Primitives.Valid.squarefree_next_degree_lt [CharZero K] {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p.Monic) (hp1 : p ≠ 1) :
    (p / ops.squarefreePart p).natDegree < p.natDegree := by
  have hd : p.natDegree ≠ 0 := mt hp.natDegree_eq_zero.mp hp1
  rw [hops.squarefree_next_eq_gcd hp.ne_zero, hops.gcd_eq, hops.derivative_eq]
  exact (natDegree_le_of_dvd (gcd_dvd_right p p.derivative)
    (derivative_ne_zero.mpr hd)).trans_lt (natDegree_derivative_lt hd)

omit [DecidableEq K] in
theorem exact_quotient_ne_zero
    {p b : Polynomial K} (hp : p ≠ 0) (hb : b ≠ 0) (hr : p % b = 0) :
    p / b ≠ 0 := by
  have he := exact_division p b hb hr
  intro hz
  rw [hz, mul_zero] at he
  exact hp he.symm

omit [DecidableEq K] in
theorem exact_quotient_degree_lt
    {p b : Polynomial K} (hp : p ≠ 0) (hb : 0 < b.natDegree)
    (hr : p % b = 0) :
    (p / b).natDegree < p.natDegree := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hq := exact_quotient_ne_zero hp hb0 hr
  have he := congrArg Polynomial.natDegree (exact_division p b hb0 hr)
  rw [natDegree_mul hb0 hq] at he
  omega

theorem Primitives.Valid.squarefreePart_squarefree {ops : Primitives K} (hops : ops.Valid)
    {p : Polynomial K} (hp : p ≠ 0) : Squarefree (ops.squarefreePart p) := by
  intro b hb
  by_contra hunit
  let g := ops.gcd p (ops.derivative p)
  have hg : g ≠ 0 := (hops.gcd_monic p (ops.derivative p) hp).ne_zero
  have hf := FiniteMultiplicity.of_not_isUnit hunit hg
  let n := _root_.multiplicity b g
  have hbg : b ^ n ∣ g := pow_multiplicity_dvd b g
  have he : g * ops.squarefreePart p = p :=
    (hops.refinement_reconstruct p (ops.derivative p) hp).1
  have hpow : b ^ (n + 2) ∣ p := by
    rw [← he, pow_add, pow_two]
    exact mul_dvd_mul hbg hb
  have hd : b ^ (n + 1) ∣ p.derivative := by
    simpa using pow_sub_one_dvd_derivative_of_pow_dvd hpow
  have hpg : b ^ (n + 1) ∣ g := by
    dsimp [g]
    rw [hops.gcd_eq, hops.derivative_eq]
    exact dvd_gcd ((pow_dvd_pow b (by omega : n + 1 ≤ n + 2)).trans hpow) hd
  exact hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self n) hpg

/-- Removing repeated factors preserves every root in characteristic zero. -/
theorem Primitives.Valid.squarefreePart_eval_eq_zero [CharZero K]
    {ops : Primitives K} (hops : ops.Valid) {p : Polynomial K} (hp : p ≠ 0) (x : K) :
    (ops.squarefreePart p).eval x = 0 ↔ p.eval x = 0 := by
  have he : ops.gcd p (ops.derivative p) * ops.squarefreePart p = p :=
    (hops.refinement_reconstruct p (ops.derivative p) hp).1
  constructor
  · intro hr
    rw [← he, eval_mul, hr, mul_zero]
  · intro hr
    have hd : ops.gcd p (ops.derivative p) ∣ p.derivative := by
      rw [hops.gcd_eq, hops.derivative_eq]
      exact gcd_dvd_right p p.derivative
    have hm : p ∣ p.derivative * ops.squarefreePart p := by
      simpa only [he] using mul_dvd_mul_right hd (ops.squarefreePart p)
    exact isRoot_of_isRoot_of_dvd_derivative_mul hp hm hr

/-- The square-free part has no repeated roots, including over field extensions. -/
theorem Primitives.Valid.squarefreePart_separable [CharZero K]
    {ops : Primitives K} (hops : ops.Valid) {p : Polynomial K} (hp : p ≠ 0) :
    (ops.squarefreePart p).Separable :=
  PerfectField.separable_iff_squarefree.mpr (hops.squarefreePart_squarefree hp)

end Gosper.ShiftlessDecomposition
