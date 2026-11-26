module

public import SympyProofs.Calculus.Antiderivative.Extension.Derivation
import Mathlib.Tactic.LinearCombination

/-! Constants of `F(θ)` over a differential field `F`. A primitive of an element with no
primitive in `F` adds no constant, and neither does an exponential of `u` when no positive
multiple of `u′` is a logarithmic derivative in `F`. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Extension

open Polynomial Differential

noncomputable local instance intAlgebraConstants {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

section Affine

variable {F : Type*} [Field F] [Differential F]

/-- The reduced numerator and denominator of a constant of `F(θ)` with `θ′ = a θ + b` are
polynomial solutions of the same homogeneous equation `P′ = (deg q) a P`, where `q` is the
denominator. -/
private theorem invariant_fraction (a b : F) (r : RatFunc F) (hr : extend (affine a b) r = 0) :
    let P := affine a b
    let c := C ((r.denom.natDegree : F) * a)
    P r.denom = c * r.denom ∧ P r.num = c * r.num := by
  let p := r.num
  let q := r.denom
  let P := affine a b
  let c := C ((q.natDegree : F) * a)
  have eqn : P p * q = p * P q := by
    apply RatFunc.algebraMap_injective F
    have hr' : extend P (algebraMap _ _ p / algebraMap _ _ q) = 0 := by
      simpa only [RatFunc.num_div_denom, p, q] using hr
    rw [extend_div] at hr'
    simp only [map_mul]
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hr').resolve_right
      (pow_ne_zero _ (RatFunc.algebraMap_ne_zero r.denom_ne_zero)))
  have dvd : q ∣ P q :=
    r.isCoprime_num_denom.symm.dvd_of_dvd_mul_left ⟨P p, eqn.symm.trans (mul_comm ..)⟩
  have hq : P q = c * q := by
    refine sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt (dvd_sub dvd (dvd_mul_left ..)) ?_)
    rw [degree_eq_natDegree r.denom_ne_zero, degree_lt_iff_coeff_zero]
    intro i hi
    change q.natDegree ≤ i at hi
    have hn : q.natDegree < i + 1 := by omega
    simp only [P, c, coeff_sub, coeff_C_mul, coeff_affine, coeff_eq_zero_of_natDegree_lt hn,
      mul_zero, add_zero]
    rcases hi.eq_or_lt with rfl | hi
    · simp [coeff_natDegree, q, r.monic_denom.leadingCoeff]
    · simp [coeff_eq_zero_of_natDegree_lt hi]
  refine ⟨hq, mul_right_cancel₀ r.denom_ne_zero ?_⟩
  rw [hq] at eqn
  exact eqn.trans (by ring)

omit [Differential F] in
/-- If every constant of a derivation of `F(θ)` has a denominator of degree zero, then
every constant lies in `F`. -/
private theorem constant_of_denom {d : Derivation ℤ (RatFunc F) (RatFunc F)}
    (hd : ∀ r, d r = 0 → r.denom.natDegree = 0) {r : RatFunc F} (hr : d r = 0) :
    ∃ c, r = RatFunc.C c := by
  rcases eq_or_ne r 0 with rfl | hn
  · exact ⟨0, (map_zero _).symm⟩
  apply (RatFunc.eq_C_iff r).mpr
  have hi : d r⁻¹ = 0 := by simp [Derivation.leibniz_inv, hr]
  have he := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (RatFunc.associated_denom_inv hn))
  exact ⟨he ▸ hd _ hi, hd _ hr⟩

/-- Let `θ′ = b` where `b` has no primitive in `F`. Then every constant of `F(θ)` lies in
`F`. -/
theorem constant_of_prim [CharZero F] {b : F} (nonprim : ¬∃ v : F, v′ = b)
    {r : RatFunc F} (hr : extend (affine 0 b) r = 0) : ∃ c, r = RatFunc.C c := by
  apply constant_of_denom (d := extend (affine 0 b)) _ hr
  intro z hz
  by_contra hn
  let q := z.denom
  have deg : 0 < q.natDegree := Nat.pos_of_ne_zero hn
  let i := q.natDegree - 1
  have succ : i + 1 = q.natDegree := Nat.sub_add_cancel deg
  have eqn := (invariant_fraction 0 b z hz).1
  have hc := congrArg (fun p : F[X] => p.coeff i) eqn
  change (affine 0 b q).coeff i = (C ((q.natDegree : F) * 0) * q).coeff i at hc
  have lc : q.leadingCoeff = 1 := z.monic_denom.leadingCoeff
  simp only [coeff_affine, succ, coeff_natDegree, lc, mul_zero, zero_mul, add_zero,
    mul_one, map_zero, coeff_zero] at hc
  apply nonprim
  refine ⟨-(q.coeff i) / (q.natDegree : F), ?_⟩
  rw [Derivation.leibniz_div_const _ _ _ (Derivation.map_natCast ..), smul_eq_mul, inv_mul_eq_div,
    map_neg, div_eq_iff (Nat.cast_ne_zero.mpr deg.ne')]
  linear_combination -hc

/-- Let `θ′ = a θ` where no positive multiple of `a` is a logarithmic derivative in `F`.
Then every constant of `F(θ)` lies in `F`. -/
theorem constant_of_exp {a : F} (h : ¬∃ (m : ℕ) (v : F), 0 < m ∧ v ≠ 0 ∧ v′ / v = (m : F) * a)
    {r : RatFunc F} (hr : extend (affine a 0) r = 0) : ∃ c, r = RatFunc.C c := by
  apply constant_of_denom (d := extend (affine a 0)) _ hr
  intro z hz
  by_contra hn
  obtain ⟨dq, dp⟩ := invariant_fraction a 0 z hz
  have vanishes (p : F[X]) (hp : affine a 0 p = C ((z.denom.natDegree : F) * a) * p) :
      p.coeff 0 = 0 := by
    by_contra hp0
    apply h
    refine ⟨_, p.coeff 0, Nat.pos_of_ne_zero hn, hp0, (div_eq_iff hp0).mpr ?_⟩
    simpa [coeff_affine] using congrArg (fun g : F[X] => g.coeff 0) hp
  exact not_isUnit_X (z.isCoprime_num_denom.isRelPrime
    (X_dvd_iff.mpr (vanishes _ dp)) (X_dvd_iff.mpr (vanishes _ dq)))

end Affine

end SympyProofs.Calculus.Antiderivative.Extension
