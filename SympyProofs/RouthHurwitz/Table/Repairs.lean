import SympyProofs.RouthHurwitz.Table.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomial identities for the exceptional Routh steps

These results apply in arbitrary degree. The signed-shift multiplier is
`1 + (-X^2)^k`; it is strictly positive on the imaginary axis.
`tableStart_axis_rootMultiplicity` and `tableStep_axis_rootMultiplicity`
connect the imaginary-axis multiplicity rules to the original input and
actual computed rows, without a regular-table hypothesis.

Right-half-plane root-count invariance under the associated deformation is a
separate analytic obligation, not asserted here. See Meinsma, "Elementary
proof of the Routh-Hurwitz test", Theorem 2.1 and Lemmas 3.1-3.2, and
Benidir/Picinbono (1990), DOI 10.1109/9.45185, Section IV.
-/

namespace RouthHurwitz
open Polynomial
open scoped ComplexConjugate

section Encoding
variable {K : Type*} [Field K]

private theorem encodeRow_add (d : ℕ) (r s : Row K) :
    encodeRow d (fun j => r j + s j) = encodeRow d r + encodeRow d s := by
  induction d using Nat.twoStepInduction generalizing r s with
  | zero => simp [encodeRow]
  | one => simp [encodeRow]; ring
  | more d ih _ => simp [encodeRow, ih]; ring

private theorem encodeRow_mul (d : ℕ) (c : K) (r : Row K) :
    encodeRow d (fun j => c * r j) = C c * encodeRow d r := by
  induction d using Nat.twoStepInduction generalizing r with
  | zero => simp [encodeRow]
  | one => simp [encodeRow]; ring
  | more d ih _ => simp [encodeRow, ih]; ring

private theorem encodeRow_raise (d k : ℕ) (r : Row K)
    (hs : ∀ j, d < 2 * j → r j = 0) :
    encodeRow (d + k) r = X ^ k * encodeRow d r := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← Nat.add_assoc, ← X_mul_encodeRow (d + k) r (fun j hj => hs j (by omega)), ih]
      ring

private theorem encodeRow_drop (d k : ℕ) (r : Row K)
    (hk : 2 * k ≤ d) (hz : ∀ j < k, r j = 0) :
    encodeRow d r = encodeRow (d - 2 * k) (fun j => r (j + k)) := by
  induction k generalizing d r with
  | zero => simp
  | succ k ih =>
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
      rw [encodeRow, hz 0 (by omega)]
      simp only [map_zero, zero_mul, zero_add]
      rw [ih (e) (fun j => r (j + 1)) (by omega) (fun j hj => hz (j + 1) (by omega))]
      congr 1
      omega

/-- The signed shift used by `repairRow` multiplies the raw row polynomial
by `1 + (-1)^k X^(2k)`. The hypotheses express leading zeros and padding,
not assumptions on root locations. -/
theorem encodeRow_shiftRow [DecidableEq K] (d w k : ℕ) (r : Row K)
    (hk : 2 * k ≤ d) (hw : d / 2 < w)
    (hz : ∀ j < k, r j = 0) (hs : ∀ j, d < 2 * j → r j = 0) :
    encodeRow d (shiftRow w k r) =
      (1 + C ((-1 : K) ^ k) * X ^ (2 * k)) * encodeRow d r := by
  have he : encodeRow d (shiftRow w k r) =
      encodeRow d (fun j => r j + (-1 : K) ^ k * r (j + k)) := by
    apply encodeRow_congr
    intro j hj
    by_cases h : j + k < w
    · simp [shiftRow, h]
    · simp [shiftRow, h, hs (j + k) (by omega)]
  rw [he, encodeRow_add, encodeRow_mul]
  have ht : ∀ j, d - 2 * k < 2 * j → r (j + k) = 0 := by
    intro j hj; apply hs; omega
  have hr := encodeRow_raise (d - 2 * k) (2 * k) (fun j => r (j + k)) ht
  rw [show d - 2 * k + 2 * k = d by omega, ← encodeRow_drop d k r hk hz] at hr
  rw [hr]
  ring

/-- Derivative replacement interpreted using the same row encoding as the
ordinary elimination and signed-shift steps. -/
theorem encodeRow_derivative (d : ℕ) (r : Row K) :
    (encodeRow d r).derivative = encodeRow (d - 1) (derivativeRow d r) := by
  induction d using Nat.twoStepInduction generalizing r with
  | zero => simp [encodeRow, derivativeRow]
  | one => simp [encodeRow, derivativeRow]
  | more d ih _ =>
      cases d with
      | zero => simp [encodeRow, derivativeRow, map_ofNat]; ring
      | succ d =>
          simp only [encodeRow, derivative_add, derivative_mul, derivative_C,
            zero_mul, zero_add, derivative_X_pow, ih]
          have he : (fun j => r (j + 1) * ((d + 1 - 2 * j : ℕ) : K)) =
              (fun j => r (j + 1) * ((d + 1 + 2 - 2 * (j + 1) : ℕ) : K)) := by
            funext j; congr 2; omega
          simp only [show d + 1 + 2 - 1 = d + 2 by omega, Nat.add_sub_cancel,
            encodeRow, derivativeRow, Nat.mul_zero, Nat.sub_zero]
          rw [← he]
          simp only [map_mul]
          congr 1
          ring

/-- The polynomial represented by every branch of the actual row repair.
No regular-table hypothesis is imposed. -/
theorem encodeRow_repairRow [DecidableEq K] (d w : ℕ) (previous raw : Row K)
    (hw : (d - 1) / 2 < w) (hs : ∀ j, d - 1 < 2 * j → raw j = 0) :
    encodeRow (d - 1) (repairRow d w previous raw) =
      if (nonzeroIndices w raw).Nonempty then
        if raw 0 = 0 then
          (1 + C ((-1 : K) ^ firstNonzero w raw) * X ^ (2 * firstNonzero w raw)) *
            encodeRow (d - 1) raw
        else encodeRow (d - 1) raw
      else (encodeRow d previous).derivative := by
  by_cases hn : (nonzeroIndices w raw).Nonempty
  · by_cases hz : raw 0 = 0
    · simp only [repairRow, ite_eq_left hn, ite_eq_left hz]
      apply encodeRow_shiftRow _ _ _ _ ?_ hw (before_firstNonzero w raw hn) hs
      by_contra! hk
      exact (firstNonzero_spec w raw hn).2 (hs _ hk)
    · simp [repairRow, hn, hz]
  · simp only [repairRow, ite_eq_right hn]
    exact (encodeRow_derivative d previous).symm

end Encoding

/-- Polynomial multiplier used to repair a row with `k` leading zeros. -/
noncomputable def shiftMultiplier (k : ℕ) : ℝ[X] := 1 + C ((-1 : ℝ) ^ k) * X ^ (2 * k)

/-- On the imaginary axis the repair multiplier is the positive real number
`1 + (ω²)^k`, including arbitrary numbers of leading zeros. -/
theorem shiftMultiplier_eval (k : ℕ) (ω : ℝ) :
    ((shiftMultiplier k).map Complex.ofRealHom).eval (ω * Complex.I) =
      ((1 + (ω ^ 2) ^ k : ℝ) : ℂ) := by
  have hsq : (ω * Complex.I : ℂ) ^ 2 = -(ω : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  simp only [shiftMultiplier, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, eval_add, eval_one,
    eval_mul, eval_pow, eval_X, map_pow, map_neg, map_one]
  rw [pow_mul, hsq, neg_pow, ← mul_assoc, ← mul_pow]
  norm_num

theorem shiftMultiplier_axis_positive (k : ℕ) (ω : ℝ) :
    0 < (((shiftMultiplier k).map Complex.ofRealHom).eval (ω * Complex.I)).re := by
  rw [shiftMultiplier_eval]
  simp only [Complex.ofReal_re]
  positivity

/-- Reflection across the imaginary axis, acting on polynomials. -/
noncomputable def axisReflect : ℂ[X] →+* ℂ[X] :=
  (compRingHom (-X)).comp (mapRingHom (starRingEnd ℂ))

private theorem axisReflect_linear (z : ℂ) (hz : z.re = 0) :
    axisReflect (X - C z) = -(X - C z) := by
  have hc : conj z = -z := by
    apply Complex.ext <;> simp [hz]
  simp [axisReflect, hc]
  ring

private theorem axis_power_dvd_reflect (p : ℂ[X]) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (h : (X - C z) ^ m ∣ p) : (X - C z) ^ m ∣ axisReflect p := by
  have hh := _root_.map_dvd axisReflect h
  rw [map_pow, axisReflect_linear z hz, neg_pow] at hh
  have he : (-1 : ℂ[X]) ^ m = C ((-1 : ℂ) ^ m) := by simp
  rw [he] at hh
  exact (C_mul_dvd (pow_ne_zero _ (by norm_num))).mp hh

/-- Opposite parity components cannot cancel on the imaginary axis, even
to higher order. This divisibility statement also handles a zero component,
whose natural-number rootMultiplicity would otherwise be misleading. -/
theorem axis_power_dvd_add_iff (p q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (z : ℂ) (hz : z.re = 0) (m : ℕ) :
    (X - C z) ^ m ∣ p + q ↔ (X - C z) ^ m ∣ p ∧ (X - C z) ^ m ∣ q := by
  constructor
  · intro h
    have hr := axis_power_dvd_reflect (p + q) z hz m h
    rw [map_add, hp, hq, ← sub_eq_add_neg, ← mul_sub] at hr
    have hd := (dvd_C_mul hσ).mp hr
    have h2p := dvd_add h hd
    have h2q := dvd_sub h hd
    have ep : p + q + (p - q) = C (2 : ℂ) * p := by simp only [map_ofNat]; ring
    have eq : p + q - (p - q) = C (2 : ℂ) * q := by simp only [map_ofNat]; ring
    rw [ep] at h2p
    rw [eq] at h2q
    exact ⟨(dvd_C_mul (by norm_num)).mp h2p, (dvd_C_mul (by norm_num)).mp h2q⟩
  · rintro ⟨hp, hq⟩; exact dvd_add hp hq

/-- Imaginary-axis multiplicity of a sum of nonzero opposite-parity
components is exactly the smaller multiplicity. -/
theorem axis_rootMultiplicity_add (p q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hs : p + q ≠ 0) (z : ℂ) (hz : z.re = 0) :
    (p + q).rootMultiplicity z = min (p.rootMultiplicity z) (q.rootMultiplicity z) := by
  apply Nat.le_antisymm
  · have hh := (axis_power_dvd_add_iff p q σ hσ hp hq z hz _).mp
      ((p + q).pow_rootMultiplicity_dvd z)
    exact le_min ((le_rootMultiplicity_iff hp0).mpr hh.1)
      ((le_rootMultiplicity_iff hq0).mpr hh.2)
  · exact rootMultiplicity_add z hs

theorem axisReflect_derivative (p : ℂ[X]) :
    axisReflect p.derivative = -(axisReflect p).derivative := by
  simp [axisReflect, derivative_comp, derivative_map]

private theorem opposite_sum_ne_zero (p q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (hp0 : p ≠ 0) : p + q ≠ 0 := by
  intro h
  have hh := congrArg axisReflect h
  rw [map_add, hp, hq, map_zero] at hh
  have he : C σ * (2 * p) = 0 := by linear_combination hh + C σ * h
  rcases mul_eq_zero.mp he with hc | hc
  · exact hσ (C_injective (hc.trans (map_zero C).symm))
  · exact hp0 ((mul_eq_zero.mp hc).resolve_left (by norm_num))

/-- For an even or odd nonconstant auxiliary polynomial, derivative repair
reduces each imaginary-axis root multiplicity by exactly one, with natural
subtraction. In particular it creates no new imaginary-axis roots. -/
theorem derivativeRepair_axis_rootMultiplicity (p : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hdegree : p.natDegree ≠ 0)
    (z : ℂ) (hz : z.re = 0) :
    (p + p.derivative).rootMultiplicity z = p.rootMultiplicity z - 1 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdegree
  have hd0 := derivative_ne_zero.mpr hdegree
  have hd : axisReflect p.derivative = -(C σ * p.derivative) := by
    rw [axisReflect_derivative, hp, derivative_C_mul]
  rw [axis_rootMultiplicity_add p p.derivative σ hσ hp hd hp0 hd0
    (opposite_sum_ne_zero p p.derivative σ hσ hp hd hp0) z hz]
  by_cases hr : p.IsRoot z
  · rw [derivative_rootMultiplicity_of_root hr]
    omega
  · rw [rootMultiplicity_eq_zero hr]
    simp

/-- Each row has the even/odd symmetry required by the general repair lemmas. -/
theorem encodeRow_axisReflect (d : ℕ) (r : Row ℝ) :
    axisReflect ((encodeRow d r).map Complex.ofRealHom) =
      C ((-1 : ℂ) ^ d) * (encodeRow d r).map Complex.ofRealHom := by
  induction d using Nat.twoStepInduction generalizing r with
  | zero => simp [encodeRow, axisReflect]
  | one => simp [encodeRow, axisReflect]
  | more d ih _ =>
      have hc (a : ℝ) : axisReflect (C (a : ℂ)) = C (a : ℂ) := by simp [axisReflect]
      have hx : axisReflect X = (-X : ℂ[X]) := by simp [axisReflect]
      simp only [encodeRow, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, map_add, map_mul, map_pow, hx, ih]
      have hn : (-X : ℂ[X]) ^ (d + 2) = C ((-1 : ℂ) ^ (d + 2)) * X ^ (d + 2) := by
        rw [neg_pow]
        simp
      have hd : (-1 : ℂ) ^ (d + 2) = (-1 : ℂ) ^ d := by rw [pow_add]; norm_num
      rw [hn, hd]
      simp only [Complex.ofRealHom_eq_coe, hc, map_pow, map_neg, map_one, pow_add]
      norm_num
      ring

/-- Ordinary elimination, including its deformation parameter, preserves
vanishing to every order on the imaginary axis. This does not require
regular pivots or any sign condition on the parameter. -/
theorem elimination_axis_power_dvd_iff (p q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (η : ℝ) (z : ℂ) (hz : z.re = 0) (m : ℕ) :
    (X - C z) ^ m ∣ (p - C (η : ℂ) * X * q) + q ↔ (X - C z) ^ m ∣ p + q := by
  have he : axisReflect (p - C (η : ℂ) * X * q) =
      C σ * (p - C (η : ℂ) * X * q) := by
    have hc : axisReflect (C (η : ℂ)) = C (η : ℂ) := by simp [axisReflect]
    have hx : axisReflect X = (-X : ℂ[X]) := by simp [axisReflect]
    rw [map_sub, map_mul, map_mul, hp, hq, hc, hx]
    ring
  rw [axis_power_dvd_add_iff _ q σ hσ he hq z hz m,
    axis_power_dvd_add_iff p q σ hσ hp hq z hz m]
  constructor
  · rintro ⟨he, hq⟩
    refine ⟨?_, hq⟩
    have hh := dvd_add he (dvd_mul_of_dvd_right hq (C (η : ℂ) * X))
    simpa using hh
  · rintro ⟨hp, hq⟩
    exact ⟨dvd_sub hp (dvd_mul_of_dvd_right hq (C (η : ℂ) * X)), hq⟩

/-- Multiplying the deficient parity component by an even factor nonzero
at the axis point preserves the multiplicity of the sum at that point. -/
theorem parityMultiplier_axis_rootMultiplicity (p q α : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (hα : axisReflect α = α) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (z : ℂ) (hz : z.re = 0) (hαz : α.eval z ≠ 0) :
    (p + α * q).rootMultiplicity z = (p + q).rootMultiplicity z := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hαz
  have haq : axisReflect (α * q) = -(C σ * (α * q)) := by
    rw [map_mul, hα, hq]; ring
  rw [axis_rootMultiplicity_add p (α * q) σ hσ hp haq hp0 (mul_ne_zero hα0 hq0)
      (opposite_sum_ne_zero p (α * q) σ hσ hp haq hp0) z hz,
    axis_rootMultiplicity_add p q σ hσ hp hq hp0 hq0
      (opposite_sum_ne_zero p q σ hσ hp hq hp0) z hz,
    rootMultiplicity_mul (mul_ne_zero hα0 hq0), rootMultiplicity_eq_zero hαz, zero_add]

private theorem encodeRow_zero (d : ℕ) : encodeRow d (fun _ => (0 : ℝ)) = 0 := by
  induction d using Nat.twoStepInduction with
  | zero => simp [encodeRow]
  | one => simp [encodeRow]
  | more d ih _ => simp [encodeRow, ih]

private theorem encodeRow_ne_zero {d : ℕ} {r : Row ℝ}
    (j : ℕ) (hj : 2 * j ≤ d) (hr : r j ≠ 0) : encodeRow d r ≠ 0 := by
  intro h
  have hh := coeff_encodeRow d r (d - 2 * j)
  rw [h, coeff_zero] at hh
  have he : d - (d - 2 * j) = 2 * j := by omega
  simp [he, show d - 2 * j ≤ d by omega] at hh
  exact hr hh.symm

private theorem shiftMultiplier_axisReflect (k : ℕ) :
    axisReflect ((shiftMultiplier k).map Complex.ofRealHom) =
      (shiftMultiplier k).map Complex.ofRealHom := by
  simp [shiftMultiplier, axisReflect, pow_mul]

/-- Effect of the actual row-repair operation on imaginary-axis multiplicity
of the polynomial represented by the preceding and current rows together.
A nonzero row's signed shift preserves multiplicity; an entirely zero row's
derivative repair removes exactly one copy of each axis root. -/
theorem repairRow_axis_rootMultiplicity (d w : ℕ) (previous raw : Row ℝ)
    (hpivot : previous 0 ≠ 0) (hw : d / 2 < w)
    (hs : ∀ j, d < 2 * j → raw j = 0) (ω : ℝ) :
    ((encodeRow (d + 1) previous + encodeRow d (repairRow (d + 1) w previous raw)).map
      Complex.ofRealHom).rootMultiplicity (ω * Complex.I) =
      if (nonzeroIndices w raw).Nonempty then
        ((encodeRow (d + 1) previous + encodeRow d raw).map Complex.ofRealHom).rootMultiplicity
          (ω * Complex.I)
      else
        ((encodeRow (d + 1) previous + encodeRow d raw).map Complex.ofRealHom).rootMultiplicity
          (ω * Complex.I) - 1 := by
  classical
  let P := (encodeRow (d + 1) previous).map Complex.ofRealHom
  let Q := (encodeRow d raw).map Complex.ofRealHom
  let σ : ℂ := (-1) ^ (d + 1)
  have hσ : σ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : axisReflect P = C σ * P := encodeRow_axisReflect (d + 1) previous
  have hq : axisReflect Q = -(C σ * Q) := by
    dsimp [Q, σ]
    rw [encodeRow_axisReflect]
    simp [pow_succ]
  have hp0 : P ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr
      (encodeRow_ne_zero 0 (by omega) hpivot)
  have hz : (ω * Complex.I : ℂ).re = 0 := by simp
  have he := encodeRow_repairRow (d + 1) w previous raw (by simpa using hw) (by simpa using hs)
  simp only [Nat.add_sub_cancel] at he
  rw [he]
  by_cases hn : (nonzeroIndices w raw).Nonempty
  · simp only [ite_eq_left hn]
    by_cases hr : raw 0 = 0
    · simp only [ite_eq_left hr]
      have hraw : encodeRow d raw ≠ 0 := by
        obtain ⟨j, hj⟩ := hn
        have hj' : j < w ∧ raw j ≠ 0 := by simpa [nonzeroIndices] using hj
        apply encodeRow_ne_zero j _ hj'.2
        by_contra! hh
        exact hj'.2 (hs j hh)
      have hαz : ((shiftMultiplier (firstNonzero w raw)).map Complex.ofRealHom).eval
          (ω * Complex.I) ≠ 0 := by
        intro hh
        have hv := shiftMultiplier_axis_positive (firstNonzero w raw) ω
        rw [hh] at hv
        simp at hv
      simpa only [P, Q, shiftMultiplier, Polynomial.map_add, Polynomial.map_mul] using
        parityMultiplier_axis_rootMultiplicity P Q _ σ hσ hp hq
          (shiftMultiplier_axisReflect _) hp0
          ((Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hraw) _ hz hαz
    · simp only [ite_eq_right hr]
  · simp only [ite_eq_right hn]
    have hraw : encodeRow d raw = 0 := by
      rw [← encodeRow_zero d]
      apply encodeRow_congr
      intro j hj
      by_contra hr
      exact hn ⟨j, by simp [nonzeroIndices, show j < w by omega, hr]⟩
    rw [hraw, add_zero, Polynomial.map_add, ← derivative_map]
    change (P + P.derivative).rootMultiplicity (ω * Complex.I) = P.rootMultiplicity (ω * Complex.I) - 1
    apply derivativeRepair_axis_rootMultiplicity P σ hσ hp _ _ hz
    have hc : P.coeff (d + 1) ≠ 0 := by
      simpa [P, coeff_map, coeff_encodeRow] using hpivot
    have hd := le_natDegree_of_ne_zero hc
    omega

/-- The ordinary elimination deformation preserves every imaginary-axis
multiplicity as long as the two polynomials being compared are nonzero. -/
theorem elimination_axis_rootMultiplicity (p q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hq : axisReflect q = -(C σ * q))
    (η : ℝ) (hs : p + q ≠ 0) (ht : (p - C (η : ℂ) * X * q) + q ≠ 0)
    (z : ℂ) (hz : z.re = 0) :
    ((p - C (η : ℂ) * X * q) + q).rootMultiplicity z = (p + q).rootMultiplicity z := by
  apply Nat.le_antisymm
  · apply (le_rootMultiplicity_iff hs).mpr
    exact (elimination_axis_power_dvd_iff p q σ hσ hp hq η z hz _).mp
      (pow_rootMultiplicity_dvd _ z)
  · apply (le_rootMultiplicity_iff ht).mpr
    exact (elimination_axis_power_dvd_iff p q σ hσ hp hq η z hz _).mpr
      (pow_rootMultiplicity_dvd _ z)

/-- One complete elimination-and-repair step, including exceptional rows,
tracks imaginary-axis multiplicities without a regular-table hypothesis. -/
theorem eliminationRepair_axis_rootMultiplicity (d w : ℕ) (upper lower : Row ℝ)
    (hu0 : upper 0 ≠ 0) (hv0 : lower 0 ≠ 0) (hw : d / 2 < w)
    (hu : ∀ j, d + 2 < 2 * j → upper j = 0)
    (hv : ∀ j, d + 1 < 2 * j → lower j = 0) (ω : ℝ) :
    let raw := boundedNextRow w upper lower
    ((encodeRow (d + 1) lower + encodeRow d (repairRow (d + 1) w lower raw)).map
      Complex.ofRealHom).rootMultiplicity (ω * Complex.I) =
      if (nonzeroIndices w raw).Nonempty then
        ((encodeRow (d + 2) upper + encodeRow (d + 1) lower).map
          Complex.ofRealHom).rootMultiplicity (ω * Complex.I)
      else
        ((encodeRow (d + 2) upper + encodeRow (d + 1) lower).map
          Complex.ofRealHom).rootMultiplicity (ω * Complex.I) - 1 := by
  dsimp only
  let raw := boundedNextRow w upper lower
  have hr : ∀ j, d < 2 * j → raw j = 0 := by
    intro j hj
    dsimp [raw, boundedNextRow]
    split
    · exact nextRow_zero upper lower j (hu (j + 1) (by omega)) (hv (j + 1) (by omega))
    · rfl
  have hrec := encodeRow_recurrence d upper lower hv0 hv
  have he : encodeRow d (nextRow upper lower) = encodeRow d raw := by
    apply encodeRow_congr
    intro j hj
    simp [raw, boundedNextRow, show j < w by omega]
  rw [he] at hrec
  let U := (encodeRow (d + 2) upper).map Complex.ofRealHom
  let V := (encodeRow (d + 1) lower).map Complex.ofRealHom
  let W := (encodeRow d raw).map Complex.ofRealHom
  let c := upper 0 / lower 0
  have hU : axisReflect U = C ((-1 : ℂ) ^ (d + 2)) * U := encodeRow_axisReflect _ _
  have hV : axisReflect V = -(C ((-1 : ℂ) ^ (d + 2)) * V) := by
    dsimp [V]
    rw [encodeRow_axisReflect]
    simp [pow_succ]
  have hV' : axisReflect V = C ((-1 : ℂ) ^ (d + 1)) * V := encodeRow_axisReflect _ _
  have hW : axisReflect W = -(C ((-1 : ℂ) ^ (d + 1)) * W) := by
    dsimp [W]
    rw [encodeRow_axisReflect]
    simp [pow_succ]
  have hU0 : U ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr
    (encodeRow_ne_zero 0 (by omega) hu0)
  have hV0 : V ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr
    (encodeRow_ne_zero 0 (by omega) hv0)
  have huv : U + V ≠ 0 := opposite_sum_ne_zero U V _ (pow_ne_zero _ (by norm_num)) hU hV hU0
  have hvw : V + W ≠ 0 := opposite_sum_ne_zero V W _ (pow_ne_zero _ (by norm_num)) hV' hW hV0
  have hrec' : U = C (c : ℂ) * X * V + W := by
    simpa [U, V, W, c] using congrArg (Polynomial.map Complex.ofRealHom) hrec
  have hred : (U - C (c : ℂ) * X * V) + V = V + W := by rw [hrec']; ring
  have hm := elimination_axis_rootMultiplicity U V _ (pow_ne_zero _ (by norm_num)) hU hV
    c huv (hred.symm ▸ hvw) (ω * Complex.I) (by simp)
  rw [hred] at hm
  have hrepair := repairRow_axis_rootMultiplicity d w lower raw hv0 hw hr ω
  simp only [Polynomial.map_add] at hrepair ⊢
  change _ = if (nonzeroIndices w raw).Nonempty then (U + V).rootMultiplicity (ω * Complex.I)
    else (U + V).rootMultiplicity (ω * Complex.I) - 1
  change _ = if (nonzeroIndices w raw).Nonempty then (V + W).rootMultiplicity (ω * Complex.I)
    else (V + W).rootMultiplicity (ω * Complex.I) - 1 at hrepair
  simpa only [hm] using hrepair

end RouthHurwitz
