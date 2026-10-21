module

public import SympyProofs.Gosper.LinearSystem
public import SympyProofs.Gosper.Normalization

/-!
# The summability criterion

For a term ratio `ρ(n) = a(n)/a(n-1)`, write a prospective sum as
`S(n) = g(n) a(n)`. Its backward difference is `a(n)` exactly when
`ρ g - g(n-1) = ρ`. This module proves the equivalence of this rational
multiplier equation with the finite linear system constructed by Gosper.
-/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K]

theorem rationalShift_add (a b : K) (f : RatFunc K) :
    rationalShift a (rationalShift b f) = rationalShift (a + b) f := by
  conv_lhs => rw [← f.num_div_denom]
  simp only [map_div₀, rationalShift_polynomial, taylor_taylor]
  rw [← rationalShift_fraction]

@[simp] theorem rationalShift_zero (f : RatFunc K) : rationalShift 0 f = f := by
  rw [rationalShift_fraction]
  simp

/-- The rational multiplier equation for an indefinite hypergeometric sum. -/
def HasRationalAntidifference (ρ : RatFunc K) : Prop :=
  ∃ g : RatFunc K, ρ * g - rationalShift (-1) g = ρ

/-- The term ratio in equation (5). -/
def normalRatio (p q r : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (p * q) /
    algebraMap K[X] (RatFunc K) (taylor (-1) p * r)

private theorem polynomial_ne_zero (p : K[X]) (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) p ≠ 0 := by
  simpa using hp

private theorem multiplier_algebra (p q r Q P s t : K)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hP : P ≠ 0) :
    p * q / (P * r) * (Q * s / p) - q * t / P = p * q / (P * r) ↔
      p = Q * s - r * t := by
  field_simp
  exact eq_comm

/-- Equations (7) and (8) are exactly the rational multiplier equation. -/
theorem multiplier_equation_iff (p q r : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (f : RatFunc K) :
    let g := algebraMap K[X] (RatFunc K) (taylor 1 q) * f / algebraMap K[X] (RatFunc K) p
    normalRatio p q r * g - rationalShift (-1) g = normalRatio p q r ↔
      RationalSolution p q r f := by
  dsimp
  simp only [map_div₀, map_mul, rationalShift_polynomial, taylor_taylor, neg_add_cancel,
    taylor_zero]
  unfold normalRatio RationalSolution
  simp only [map_mul]
  exact multiplier_algebra _ _ _ _ _ _ _ (polynomial_ne_zero p hp)
    (polynomial_ne_zero q hq) (polynomial_ne_zero r hr)
    (polynomial_ne_zero _ ((taylor_eq_zero _ _).not.mpr hp))

theorem summable_iff_rational_solution (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    HasRationalAntidifference (normalRatio p q r) ↔
      ∃ f : RatFunc K, RationalSolution p q r f := by
  constructor
  · rintro ⟨g, hg⟩
    let f := algebraMap K[X] (RatFunc K) p * g /
      algebraMap K[X] (RatFunc K) (taylor 1 q)
    refine ⟨f, (multiplier_equation_iff p q r hp hq hr f).mp ?_⟩
    have hP := polynomial_ne_zero p hp
    have hQ := polynomial_ne_zero (taylor 1 q) ((taylor_eq_zero _ _).not.mpr hq)
    have hcancel : algebraMap K[X] (RatFunc K) (taylor 1 q) * f /
        algebraMap K[X] (RatFunc K) p = g := by dsimp [f]; field_simp
    simpa only [hcancel] using hg
  · rintro ⟨f, hf⟩
    exact ⟨_, (multiplier_equation_iff p q r hp hq hr f).mpr hf⟩

variable [DecidableEq K]

/-- Gosper's complete criterion, with the paper's signed bound and rejection test. -/
theorem gosper_criterion [CharZero K] (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : ShiftCoprime q r) :
    HasRationalAntidifference (normalRatio p q r) ↔
      let k := paperDegreeBound p (taylor 1 q) r
      0 ≤ k ∧ ∃ c, (coefficientMatrix p q r k.toNat).mulVec c =
        toFn (equationDegree p q r k.toNat + 1) p := by
  rw [summable_iff_rational_solution p q r hp hq hr,
    rational_solution_iff_paperLinearSystem p q r hp hq hr hqr]

/-- Every nonzero rational term ratio can be normalized and then decided by
the finite linear-system criterion. -/
theorem exists_normalized_criterion [CharZero K] (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ p q r : K[X], p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ ShiftCoprime q r ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B = normalRatio p q r ∧
      (HasRationalAntidifference (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B) ↔
        let k := paperDegreeBound p (taylor 1 q) r
        0 ≤ k ∧ ∃ c, (coefficientMatrix p q r k.toNat).mulVec c =
          toFn (equationDegree p q r k.toNat + 1) p) := by
  obtain ⟨p, q, r, hp, hq, hr, hqr, he⟩ := exists_normalForm A B hA hB
  have hratio : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B =
      normalRatio p q r := by
    apply (div_eq_div_iff (polynomial_ne_zero B hB)
      (polynomial_ne_zero _ (mul_ne_zero ((taylor_eq_zero _ _).not.mpr hp) hr))).mpr
    simpa only [← map_mul, mul_comm] using congrArg (algebraMap K[X] (RatFunc K)) he
  exact ⟨p, q, r, hp, hq, hr, hqr, hratio, hratio ▸ gosper_criterion p q r hp hq hr hqr⟩

end Gosper
