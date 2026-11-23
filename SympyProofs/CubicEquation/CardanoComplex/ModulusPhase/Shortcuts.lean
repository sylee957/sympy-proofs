module

public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Monic

/-!
# Simpler forms of the monic modulus-and-phase formula

Write `p`, `q` for the depressed coefficients of `x^3 + a*x^2 + b*x + c` and
`A = -q/2 + sqrt Δ` for the first radicand. When something is known about them,
`modulusPhaseMonicCubicRoots a b c` equals a simpler formula, field by field
and in the same order.

* If `A ≠ 0`, in particular if `p ≠ 0`, it equals `quotientMonicCubicRoots`,
  whose second radical is `-p / (3 * u)`.
* If `A` is not a nonpositive real, in particular if `q` has negative real
  part, it equals `principalQuotientMonicCubicRoots`, which also takes the
  first radical as a principal cube root.
* If `p = 0`, the solutions are the three cube roots of `-q`. The order of the
  last two depends on whether `A = 0`, which `radicandPlus_eq_zero_iff`
  expresses through the half-plane of `q`.
* If `a = 0`, there is no shift.

The reductions for real coefficients are in `ModulusPhase/Realness.lean`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open Complex
open scoped ComplexConjugate

/-! ### The principal square root -/

/-- The principal square root lies in the closed right half-plane. -/
theorem sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  have h := Complex.cpow_ofReal_re z (2⁻¹ : ℝ)
  rw [show ((2⁻¹ : ℝ) : ℂ) = (2⁻¹ : ℂ) by simp] at h
  rw [Complex.sqrt, h]
  refine mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
    (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
  · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
  · linarith [Complex.arg_le_pi z, Real.pi_pos]

/-- On the imaginary axis the principal square root has nonnegative imaginary part. -/
theorem sqrt_im_nonneg_of_re_eq_zero {z : ℂ} (h : (Complex.sqrt z).re = 0) :
    0 ≤ (Complex.sqrt z).im := by
  have hre := Complex.cpow_ofReal_re z (2⁻¹ : ℝ)
  have him := Complex.cpow_ofReal_im z (2⁻¹ : ℝ)
  rw [show ((2⁻¹ : ℝ) : ℂ) = (2⁻¹ : ℂ) by simp] at hre him
  rw [Complex.sqrt] at h ⊢
  rw [hre] at h
  rw [him]
  rcases mul_eq_zero.mp h with h0 | h0
  · rw [h0, zero_mul]
  · have hle : arg z * 2⁻¹ ≤ Real.pi / 2 := by linarith [Complex.arg_le_pi z]
    have hlt : -(Real.pi / 2) < arg z * 2⁻¹ := by linarith [Complex.neg_pi_lt_arg z]
    rcases hle.lt_or_eq with hl | he
    · exact absurd h0 (Real.cos_pos_of_mem_Ioo ⟨hlt, hl⟩).ne'
    · rw [he, Real.sin_pi_div_two, mul_one]
      exact Real.rpow_nonneg (norm_nonneg z) _

/-- The principal square root of `z^2` is `z` exactly on the right half-plane,
with the nonnegative imaginary axis included. -/
theorem sqrt_sq_eq_self_iff (z : ℂ) :
    Complex.sqrt (z ^ 2) = z ↔ 0 < z.re ∨ (z.re = 0 ∧ 0 ≤ z.im) := by
  constructor
  · intro h
    have hre := sqrt_re_nonneg (z ^ 2)
    rw [h] at hre
    rcases hre.lt_or_eq with hpos | h0
    · exact Or.inl hpos
    · refine Or.inr ⟨h0.symm, ?_⟩
      have him := sqrt_im_nonneg_of_re_eq_zero (z := z ^ 2) (by rw [h]; exact h0.symm)
      rwa [h] at him
  · intro hz
    have hsq : Complex.sqrt (z ^ 2) ^ 2 = z ^ 2 := sqrt_sq _
    have hfac : (Complex.sqrt (z ^ 2) - z) * (Complex.sqrt (z ^ 2) + z) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact sub_eq_zero.mp h1
    · have hs : Complex.sqrt (z ^ 2) = -z := eq_neg_of_add_eq_zero_left h1
      have hre := sqrt_re_nonneg (z ^ 2)
      rw [hs, neg_re] at hre
      rcases hz with hpos | ⟨h0, him⟩
      · linarith
      · have him' := sqrt_im_nonneg_of_re_eq_zero (z := z ^ 2) (by rw [hs, neg_re, h0, neg_zero])
        rw [hs, neg_im] at him'
        have hz0 : z = 0 := Complex.ext h0 (by simpa using le_antisymm (by linarith) him)
        rw [hz0]
        simp

/-! ### The first radicand -/

/-- A nonzero linear coefficient makes the first radicand nonzero. -/
theorem radicandPlus_ne_zero_of_ne_zero {p : ℂ} (hp : p ≠ 0) (q : ℂ) : radicandPlus p q ≠ 0 := by
  have h : radicandPlus p q * radicandMinus p q ≠ 0 := by
    rw [radicands_product]
    exact pow_ne_zero 3 (div_ne_zero (neg_ne_zero.mpr hp) (by norm_num))
  exact left_ne_zero_of_mul h

/-- The first radicand vanishes exactly when `p = 0` and `q` lies in the right
half-plane, with the nonnegative imaginary axis included. -/
theorem radicandPlus_eq_zero_iff (p q : ℂ) :
    radicandPlus p q = 0 ↔ p = 0 ∧ (0 < q.re ∨ (q.re = 0 ∧ 0 ≤ q.im)) := by
  have hre : (q / 2).re = q.re / 2 := by simp
  have him : (q / 2).im = q.im / 2 := by simp
  have hhalf : (0 < (q / 2).re ∨ ((q / 2).re = 0 ∧ 0 ≤ (q / 2).im)) ↔
      (0 < q.re ∨ (q.re = 0 ∧ 0 ≤ q.im)) := by
    rw [hre, him]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
  have key : radicandPlus 0 q = 0 ↔ Complex.sqrt ((q / 2) ^ 2) = q / 2 := by
    have hD : discriminant 0 q = (q / 2) ^ 2 := by unfold discriminant; ring
    rw [radicandPlus, hD]
    constructor <;> intro h <;> linear_combination h
  constructor
  · intro hA
    have hp : p = 0 := by
      by_contra hp
      exact radicandPlus_ne_zero_of_ne_zero hp q hA
    subst hp
    exact ⟨rfl, hhalf.mp ((sqrt_sq_eq_self_iff _).mp (key.mp hA))⟩
  · rintro ⟨rfl, hq⟩
    exact key.mpr ((sqrt_sq_eq_self_iff _).mpr (hhalf.mpr hq))

/-- A constant coefficient with negative real part puts the first radicand in
the open right half-plane. -/
theorem radicandPlus_mem_slitPlane_of_re_neg (p : ℂ) {q : ℂ} (hq : q.re < 0) :
    radicandPlus p q ∈ slitPlane := by
  have hre : (-q / 2).re = -q.re / 2 := by simp
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [radicandPlus, add_re, hre]
  linarith [sqrt_re_nonneg (discriminant p q)]

/-- A constant coefficient on the negative imaginary axis makes the first
radicand nonzero. -/
theorem radicandPlus_ne_zero_of_re_eq_zero_of_im_neg (p : ℂ) {q : ℂ}
    (hre : q.re = 0) (him : q.im < 0) : radicandPlus p q ≠ 0 := by
  intro hA
  obtain ⟨-, hq⟩ := (radicandPlus_eq_zero_iff p q).mp hA
  rcases hq with hq | ⟨-, hq⟩ <;> linarith

/-! ### The second radicand -/

/-- A constant coefficient with positive real part makes the second radicand
nonzero. -/
theorem radicandMinus_ne_zero_of_re_pos (p : ℂ) {q : ℂ} (hq : 0 < q.re) :
    radicandMinus p q ≠ 0 := by
  intro h
  have hhalf : (-q / 2).re = -q.re / 2 := by simp
  have hre : (radicandMinus p q).re =
      -q.re / 2 - (Complex.sqrt (discriminant p q)).re := by
    rw [radicandMinus, sub_re, hhalf]
  rw [h, zero_re] at hre
  linarith [sqrt_re_nonneg (discriminant p q)]

/-- A constant coefficient on the positive imaginary axis makes the second
radicand nonzero. -/
theorem radicandMinus_ne_zero_of_re_eq_zero_of_im_pos (p : ℂ) {q : ℂ}
    (hre : q.re = 0) (him : 0 < q.im) : radicandMinus p q ≠ 0 := by
  intro hB
  have hs : Complex.sqrt (discriminant p q) = -q / 2 := by
    rw [radicandMinus] at hB
    exact (sub_eq_zero.mp hB).symm
  have hre' : (-q / 2).re = -q.re / 2 := by simp
  have him' : (-q / 2).im = -q.im / 2 := by simp
  have hnonneg := sqrt_im_nonneg_of_re_eq_zero (z := discriminant p q)
    (by rw [hs, hre', hre]; norm_num)
  rw [hs, him'] at hnonneg
  linarith

/-! ### A nonzero first radicand: the second radical is a quotient -/

/-- When the first radicand is nonzero, the second radical is `-p / (3 * u)`. -/
theorem modulusPhaseV_of_ne_zero {p q : ℂ} (h : radicandPlus p q ≠ 0) :
    modulusPhaseV p q = -p / (3 * modifiedPrincipal (radicandPlus p q)) := by
  have hu : modifiedPrincipal (radicandPlus p q) ≠ 0 := fun hu =>
    h (modifiedPrincipal_eq_zero_iff.mp hu)
  rw [modulusPhaseV_eq, modifiedConjugateCorrectedU, ite_eq_right hu, div_div]

/-- When the first radicand vanishes, the second radical is the modified
principal cube root of `-q`. -/
theorem modulusPhaseV_of_eq_zero {p q : ℂ} (h : radicandPlus p q = 0) :
    modulusPhaseV p q = modifiedPrincipal (-q) := by
  have hB : radicandMinus p q = -q := by
    have hsum := radicands_sum p q
    rwa [h, zero_add] at hsum
  rw [modulusPhaseV_eq, modifiedConjugateCorrectedU,
    ite_eq_left (modifiedPrincipal_eq_zero_iff.mpr h), hB]

/-- Cardano's formula for `x^3 + a*x^2 + b*x + c = 0` with the second radical
taken as the quotient `-p / (3 * u)`. It agrees with
`modulusPhaseMonicCubicRoots` when the first radicand is nonzero. -/
def quotientMonicCubicRoots (a b c : ℂ) : CardanoRoots :=
  let p := b - a ^ 2 / 3
  let q := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  let u := modifiedPrincipal (-q / 2 + Complex.sqrt Δ)
  let v := -p / (3 * u)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift := a / 3
  { x₀ := u + v - shift
    x₁ := ω * u + ω ^ 2 * v - shift
    x₂ := ω ^ 2 * u + ω * v - shift }

/-- For a nonzero first radicand the second radical can be taken as a quotient. -/
theorem modulusPhaseMonicCubicRoots_eq_quotient {a b c : ℂ}
    (h : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    modulusPhaseMonicCubicRoots a b c = quotientMonicCubicRoots a b c := by
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, modulusPhaseV_of_ne_zero h]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, modulusPhaseV_of_ne_zero h]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, modulusPhaseV_of_ne_zero h]
    rfl

/-- For a nonzero depressed linear coefficient the second radical can be taken
as a quotient. -/
theorem modulusPhaseMonicCubicRoots_eq_quotient_of_ne_zero {a b c : ℂ}
    (h : complexMonicDepressedP a b ≠ 0) :
    modulusPhaseMonicCubicRoots a b c = quotientMonicCubicRoots a b c :=
  modulusPhaseMonicCubicRoots_eq_quotient (radicandPlus_ne_zero_of_ne_zero h _)

/-! ### A first radicand off the branch cut: principal cube root and quotient -/

/-- Cardano's formula for `x^3 + a*x^2 + b*x + c = 0` with the first radical a
principal cube root and the second the quotient `-p / (3 * u)`. It agrees with
`modulusPhaseMonicCubicRoots` when the first radicand is not a nonpositive real. -/
def principalQuotientMonicCubicRoots (a b c : ℂ) : CardanoRoots :=
  let p := b - a ^ 2 / 3
  let q := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  let u := principal (-q / 2 + Complex.sqrt Δ)
  let v := -p / (3 * u)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift := a / 3
  { x₀ := u + v - shift
    x₁ := ω * u + ω ^ 2 * v - shift
    x₂ := ω ^ 2 * u + ω * v - shift }

/-- For a first radicand that is not a nonpositive real, the formula is the
quotient formula with a principal cube root. -/
theorem modulusPhaseMonicCubicRoots_eq_principalQuotient {a b c : ℂ}
    (h : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ∈ slitPlane) :
    modulusPhaseMonicCubicRoots a b c = principalQuotientMonicCubicRoots a b c := by
  have h0 := slitPlane_ne_zero h
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, modulusPhaseV_of_ne_zero h0,
      modifiedConjugateCorrectedU, modifiedPrincipal_eq_principal h]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, modulusPhaseV_of_ne_zero h0,
      modifiedConjugateCorrectedU, modifiedPrincipal_eq_principal h]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, modulusPhaseV_of_ne_zero h0,
      modifiedConjugateCorrectedU, modifiedPrincipal_eq_principal h]
    rfl

/-- When the depressed constant coefficient has negative real part, the formula
is the quotient formula with a principal cube root. -/
theorem modulusPhaseMonicCubicRoots_eq_principalQuotient_of_re_neg {a b c : ℂ}
    (h : (complexMonicDepressedQ a b c).re < 0) :
    modulusPhaseMonicCubicRoots a b c = principalQuotientMonicCubicRoots a b c :=
  modulusPhaseMonicCubicRoots_eq_principalQuotient (radicandPlus_mem_slitPlane_of_re_neg _ h)

/-! ### The formula built on the second radicand -/

/-- Cardano's formula for `x^3 + a*x^2 + b*x + c = 0` built on the second
radicand `B = -q/2 - sqrt Δ`: the second radical is `v = -(-B)^(1/3)` with a
principal cube root, and the first is the quotient `-p / (3 * v)`. -/
def secondRadicandQuotientMonicCubicRoots (a b c : ℂ) : CardanoRoots :=
  let p := b - a ^ 2 / 3
  let q := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  let v := -principal (-(-q / 2 - Complex.sqrt Δ))
  let u := -p / (3 * v)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift := a / 3
  { x₀ := u + v - shift
    x₁ := ω * u + ω ^ 2 * v - shift
    x₂ := ω ^ 2 * u + ω * v - shift }

/-! ### A vanishing depressed linear coefficient: the cube roots of `-q` -/

/-- When the first radicand vanishes, the solutions are the cube roots of `-q`
in the order `t`, `ω^2 * t`, `ω * t`. -/
theorem modulusPhaseMonicCubicRoots_of_radicandPlus_eq_zero {a b c : ℂ}
    (h : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0) :
    modulusPhaseMonicCubicRoots a b c =
      { x₀ := modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3
        x₁ := omega ^ 2 * modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3
        x₂ := omega * modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3 } := by
  have hu : modifiedConjugateCorrectedU (complexMonicDepressedP a b)
      (complexMonicDepressedQ a b c) = 0 := modifiedPrincipal_eq_zero_iff.mpr h
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, modulusPhaseV_of_eq_zero h, hu, zero_add]
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, modulusPhaseV_of_eq_zero h, hu, mul_zero, zero_add]
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, modulusPhaseV_of_eq_zero h, hu, mul_zero, zero_add]

/-- When `p = 0` and the first radicand is nonzero, the solutions are the cube
roots of `-q` in the order `t`, `ω * t`, `ω^2 * t`. -/
theorem modulusPhaseMonicCubicRoots_of_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b = 0)
    (h : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    modulusPhaseMonicCubicRoots a b c =
      { x₀ := modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3
        x₁ := omega * modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3
        x₂ := omega ^ 2 * modifiedPrincipal (-complexMonicDepressedQ a b c) - a / 3 } := by
  have hB : radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0 := by
    have hprod := radicands_product (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
    rw [hp] at hprod ⊢
    have hzero : radicandPlus 0 (complexMonicDepressedQ a b c) *
        radicandMinus 0 (complexMonicDepressedQ a b c) = 0 := by rw [hprod]; simp
    rw [hp] at h
    exact (mul_eq_zero.mp hzero).resolve_left h
  have hA : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) =
      -complexMonicDepressedQ a b c := by
    have hsum := radicands_sum (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
    rwa [hB, add_zero] at hsum
  have hv : modulusPhaseV (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0 := by
    rw [modulusPhaseV_of_ne_zero h, hp]
    simp
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, hv, add_zero, modifiedConjugateCorrectedU, hA]
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, hv, mul_zero, add_zero,
      modifiedConjugateCorrectedU, hA]
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, hv, mul_zero, add_zero,
      modifiedConjugateCorrectedU, hA]

/-! ### No quadratic term: no shift -/

/-- For a depressed cubic `x^3 + p*x + q` the three solutions are the Cardano
values of the two radicals, with no shift. -/
theorem modulusPhaseMonicCubicRoots_zero (p q : ℂ) :
    modulusPhaseMonicCubicRoots 0 p q =
      { x₀ := modifiedConjugateCorrectedU p q + modulusPhaseV p q
        x₁ := omega * modifiedConjugateCorrectedU p q + omega ^ 2 * modulusPhaseV p q
        x₂ := omega ^ 2 * modifiedConjugateCorrectedU p q + omega * modulusPhaseV p q } := by
  have hP : complexMonicDepressedP 0 p = p := by simp [complexMonicDepressedP]
  have hQ : complexMonicDepressedQ 0 p q = q := by simp [complexMonicDepressedQ]
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, hP, hQ, zero_div, sub_zero]
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, hP, hQ, zero_div, sub_zero]
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, hP, hQ, zero_div, sub_zero]

end CubicEquation.CardanoComplex
