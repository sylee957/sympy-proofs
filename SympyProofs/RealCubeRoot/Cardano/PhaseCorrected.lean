module

public import SympyProofs.RealCubeRoot.Cardano.Principal
public import Mathlib.Algebra.Order.Round
public import Mathlib.Basic.Real.Sign

/-!
# Three phase-corrected versions of Cardano's formula

For arbitrary complex coefficients, take principal cube roots of the two
Cardano radicands `A` and `B`. Since `A * B = C^3`, where `C = -p/3`, multiplying
the second root by `omega ^ round ((3*arg C - arg A - arg B) / (2*pi))`
makes their product equal to `C`.

The round and floor versions use Mathlib's principal argument: `-pi < arg z <= pi`,
negative real inputs have argument `pi`, and `arg 0 = 0`. Rounding is to the nearest
integer with ties toward positive infinity, equivalently `floor (t + 1/2)`.
These conventions are stated in `principal_arg_conventions`, `round_eq_piecewise`,
and `round_half_tie_up`.

The sign version instead uses `Z = C * conj (principal A * principal B)` and
`n = (1 - sign (re Z)) * sign (im Z) / 2`. The real sign function takes values
`-1`, `0`, and `1`, with `sign 0 = 0`. On the required inputs, `n` is `0`, `1`, or
`-1`; no argument value at zero is needed by this correction.

All three formulas have no explicit case split or division by a radical.
Their floor, round, or sign operations still select branches. They cover
arbitrary complex coefficients and repeated and triple roots. The full formulas
are `cardano_formula_phaseCorrected_round`, `cardano_formula_phaseCorrected_floor`,
and `cardano_formula_phaseCorrected_sign`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- The argument conventions used by the round and floor formulas: zero has
argument zero, the range is `(-pi, pi]`, and negative real inputs use `pi`. -/
theorem principal_arg_conventions :
    Complex.arg 0 = 0 ∧
    (∀ z : ℂ, -Real.pi < z.arg ∧ z.arg ≤ Real.pi) ∧
    (∀ x : ℝ, x < 0 → Complex.arg (x : ℂ) = Real.pi) :=
  ⟨Complex.arg_zero, fun z => ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩,
    fun _ hx => Complex.arg_ofReal_of_neg hx⟩

theorem omega_eq_exp : omega = Complex.exp ((2 * Real.pi * I) / 3) := by
  have h : (2 * (Real.pi : ℂ) * I) / 3 = ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega
  push_cast
  ring

@[simp] theorem omega_zpow_cube (n : ℤ) : (omega ^ n) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul', zpow_mul, zpow_natCast, omega_cube, one_zpow]

/-- Round down below the midpoint and up at or above it. In particular, ties
go toward positive infinity, including for negative inputs. -/
theorem round_eq_piecewise (t : ℝ) :
    round t = if t - (⌊t⌋ : ℝ) < 1 / 2 then ⌊t⌋ else ⌊t⌋ + 1 := by
  rw [round_eq]
  have hlo := Int.floor_le t
  have hhi := Int.lt_floor_add_one t
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

/-- Every exact halfway case chooses the larger integer: for example,
`round (1/2) = 1` and `round (-1/2) = 0`. -/
theorem round_half_tie_up (n : ℤ) : round ((n : ℝ) + 1 / 2) = n + 1 := by
  rw [round_intCast_add]
  norm_num [round_eq]

/-- The integer correction for two principal cube roots whose radicands multiply to `C^3`.
This is defined even when one or more inputs are zero. Halfway ties round up,
as made explicit in `phaseIndex_eq_piecewise`. -/
def phaseIndex (A B C : ℂ) : ℤ :=
  round ((3 * C.arg - A.arg - B.arg) / (2 * Real.pi))

/-- The phase correction using only floor, with halfway ties still rounded up. -/
theorem phaseIndex_eq_floor (A B C : ℂ) :
    phaseIndex A B C = ⌊(3 * C.arg - A.arg - B.arg) / (2 * Real.pi) + 1 / 2⌋ :=
  round_eq _

/-- The piecewise form of the phase correction, with its tie convention visible. -/
theorem phaseIndex_eq_piecewise (A B C : ℂ) :
    let t := (3 * C.arg - A.arg - B.arg) / (2 * Real.pi)
    phaseIndex A B C = if t - (⌊t⌋ : ℝ) < 1 / 2 then ⌊t⌋ else ⌊t⌋ + 1 :=
  round_eq_piecewise _

/-- For a nonzero product, the rounded expression is the exact integer relating
the principal logarithms. -/
theorem phaseIndex_log_identity {A B C : ℂ} (hAB : A * B = C ^ 3) (hC : C ≠ 0) :
    3 * Complex.log C = Complex.log A + Complex.log B +
      (phaseIndex A B C : ℂ) * (2 * Real.pi * I) := by
  have hAB0 : A * B ≠ 0 := by rw [hAB]; exact pow_ne_zero _ hC
  have hA : A ≠ 0 := (mul_ne_zero_iff.mp hAB0).1
  have hB : B ≠ 0 := (mul_ne_zero_iff.mp hAB0).2
  have he : Complex.exp (3 * Complex.log C) =
      Complex.exp (Complex.log A + Complex.log B) := by
    rw [Complex.exp_add, Complex.exp_log hA, Complex.exp_log hB,
      show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul,
      Complex.exp_log hC, hAB]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hn
  norm_num [Complex.mul_im, Complex.mul_re, Complex.log_im] at him
  have hnarg : (3 * C.arg - A.arg - B.arg) / (2 * Real.pi) = (n : ℝ) := by
    apply (div_eq_iff (ne_of_gt Real.two_pi_pos)).mpr
    linarith
  simpa only [phaseIndex, hnarg, round_intCast] using hn

/-- The phase correction enforces the compatible product, including zero radicands. -/
theorem phaseCorrected_product {A B C : ℂ} (hAB : A * B = C ^ 3) :
    principal A * (omega ^ phaseIndex A B C * principal B) = C := by
  by_cases hC : C = 0
  · have hzero : A = 0 ∨ B = 0 := by simpa [hC] using hAB
    rcases hzero with rfl | rfl <;> simp [principal, hC]
  · have hAB0 : A * B ≠ 0 := by rw [hAB]; exact pow_ne_zero _ hC
    have hA : A ≠ 0 := (mul_ne_zero_iff.mp hAB0).1
    have hB : B ≠ 0 := (mul_ne_zero_iff.mp hAB0).2
    have hlog := phaseIndex_log_identity hAB hC
    rw [principal, principal, Complex.cpow_def_of_ne_zero hA,
      Complex.cpow_def_of_ne_zero hB, omega_eq_exp, ← Complex.exp_int_mul,
      ← Complex.exp_add, ← Complex.exp_add]
    have he : Complex.log A * (3⁻¹ : ℂ) +
        ((phaseIndex A B C : ℂ) * (2 * Real.pi * I / 3) +
          Complex.log B * (3⁻¹ : ℂ)) = Complex.log C := by
      linear_combination -hlog / 3
    rw [he, Complex.exp_log hC]

/-- The second radical, paired by an integer phase rather than division by the first. -/
def phaseCorrectedV (p q : ℂ) : ℂ :=
  omega ^ phaseIndex (radicandPlus p q) (radicandMinus p q) (-p / 3) *
    principal (radicandMinus p q)

@[simp] theorem phaseCorrectedV_cube (p q : ℂ) :
    phaseCorrectedV p q ^ 3 = radicandMinus p q := by
  simp [phaseCorrectedV, mul_pow]

theorem phaseCorrected_uv (p q : ℂ) : u p q * phaseCorrectedV p q = -p / 3 :=
  phaseCorrected_product (radicands_product p q)

def phaseCorrectedDepressedRoots (p q : ℂ) : List ℂ :=
  pairedRoots (u p q) (phaseCorrectedV p q)

theorem mem_phaseCorrectedDepressedRoots_iff (p q x : ℂ) :
    x ∈ phaseCorrectedDepressedRoots p q ↔ x ^ 3 + p * x + q = 0 := by
  apply mem_pairedRoots_iff
  · rw [u_cube, phaseCorrectedV_cube, radicands_sum]
  · exact phaseCorrected_uv p q

/-- Exact factorization also records the multiplicities of the three roots. -/
theorem phaseCorrected_depressed_factorization (p q x : ℂ) :
    (x - (u p q + phaseCorrectedV p q)) *
      (x - (omega * u p q + omega ^ 2 * phaseCorrectedV p q)) *
      (x - (omega ^ 2 * u p q + omega * phaseCorrectedV p q)) =
        x ^ 3 + p * x + q := by
  rw [factorization_identity, phaseCorrected_uv, u_cube, phaseCorrectedV_cube, radicands_sum]
  ring

def phaseCorrectedCubicRoots (a b c d : ℂ) : List ℂ :=
  (phaseCorrectedDepressedRoots (depressedP a b c) (depressedQ a b c d)).map
    (fun z => z - (b / a) / 3)

theorem mem_phaseCorrectedCubicRoots_iff {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    x ∈ phaseCorrectedCubicRoots a b c d ↔
      a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  have hmem : x ∈ phaseCorrectedCubicRoots a b c d ↔
      x + (b / a) / 3 ∈
        phaseCorrectedDepressedRoots (depressedP a b c) (depressedQ a b c d) := by
    simp only [phaseCorrectedCubicRoots, List.mem_map]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : x + (b / a) / 3 = y := by linear_combination -heq
      rwa [hxy]
    · intro hx
      exact ⟨x + (b / a) / 3, hx, by ring⟩
  rw [hmem, mem_phaseCorrectedDepressedRoots_iff, depressed_shift]
  have hscale : a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
      a * x ^ 3 + b * x ^ 2 + c * x + d := by
    field_simp
  rw [← hscale, mul_eq_zero]
  simp [ha]

/-- A phase selector with no argument calls. `Real.sign` is `-1` on negative
inputs, `0` at zero, and `1` on positive inputs. On the three cube-root-of-unity
rays this expression takes the integer values `0`, `1`, and `-1`. -/
def signPhase (z : ℂ) : ℝ := (1 - Real.sign z.re) * Real.sign z.im / 2

@[simp] theorem signPhase_ofReal (r : ℝ) : signPhase (r : ℂ) = 0 := by
  simp [signPhase]

theorem signPhase_omega_mul {r : ℝ} (hr : 0 < r) : signPhase (omega * r) = 1 := by
  have hre : (omega * r).re < 0 := by
    simp [omega, Complex.mul_re]
    linarith
  have him : 0 < (omega * r).im := by
    simp [omega, Complex.mul_im]
    positivity
  rw [signPhase, Real.sign_of_neg hre, Real.sign_of_pos him]
  norm_num

theorem signPhase_omega_sq_mul {r : ℝ} (hr : 0 < r) :
    signPhase (omega ^ 2 * r) = -1 := by
  have hre : (omega ^ 2 * r).re < 0 := by
    rw [omega_sq]
    simp [omega, Complex.mul_re]
    linarith
  have him : (omega ^ 2 * r).im < 0 := by
    rw [omega_sq]
    simp [omega, Complex.mul_im]
    have : 0 < Real.sqrt 3 * r := mul_pos (by positivity) hr
    nlinarith
  rw [signPhase, Real.sign_of_neg hre, Real.sign_of_neg him]
  norm_num

/-- Two numbers with equal cubes differ by one of the three cube roots of unity. -/
theorem cube_eq_cube_iff (C W : ℂ) :
    C ^ 3 = W ^ 3 ↔ C = W ∨ C = omega * W ∨ C = omega ^ 2 * W := by
  have hfactor := factorization_identity C W 0
  simp only [mul_zero, zero_mul, add_zero, zero_pow (by decide : 3 ≠ 0), sub_zero] at hfactor
  rw [← sub_eq_zero, ← hfactor]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]

/-- The sign expression selects `0`, `1`, or `-1` according to the required
correction. If both numbers are zero, it selects `0`. -/
theorem signPhase_pair_spec {W C : ℂ} (h : C ^ 3 = W ^ 3) :
    (signPhase (C * conj W) = 0 ∧ C = W) ∨
    (signPhase (C * conj W) = 1 ∧ C = omega * W) ∨
    (signPhase (C * conj W) = -1 ∧ C = omega ^ 2 * W) := by
  by_cases hW : W = 0
  · have hC : C = 0 := by simpa [hW] using h
    simp [hW, hC, signPhase]
  · have hr : 0 < normSq W := normSq_pos.mpr hW
    rcases (cube_eq_cube_iff C W).mp h with rfl | rfl | rfl
    · exact Or.inl ⟨by rw [mul_conj]; exact signPhase_ofReal _, rfl⟩
    · exact Or.inr (Or.inl
        ⟨by rw [mul_assoc, mul_conj]; exact signPhase_omega_mul hr, rfl⟩)
    · exact Or.inr (Or.inr
        ⟨by rw [mul_assoc, mul_conj]; exact signPhase_omega_sq_mul hr, rfl⟩)

theorem omega_inv_eq_sq : omega⁻¹ = omega ^ 2 := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [← pow_succ] using omega_cube

/-- The real-valued sign expression is integer-valued on these inputs, so its
complex power of `omega` is the appropriate cube root of unity. -/
theorem signPhase_corrects_cube {W C : ℂ} (h : C ^ 3 = W ^ 3) :
    (omega ^ (signPhase (C * conj W) : ℂ)) ^ 3 = 1 ∧
      omega ^ (signPhase (C * conj W) : ℂ) * W = C := by
  rcases signPhase_pair_spec h with ⟨hn, hC⟩ | ⟨hn, hC⟩ | ⟨hn, hC⟩
  · rw [hn]
    simp [hC]
  · rw [hn]
    simp [hC]
  · rw [hn]
    simp only [ofReal_neg, ofReal_one, Complex.cpow_neg_one, inv_pow, omega_cube,
      inv_one, true_and]
    rw [omega_inv_eq_sq]
    exact hC.symm

/-- The second principal radical paired using real and imaginary parts and sign. -/
def signCorrectedV (p q : ℂ) : ℂ :=
  let U := principal (radicandPlus p q)
  let V := principal (radicandMinus p q)
  let Z := (-p / 3) * conj (U * V)
  omega ^ (signPhase Z : ℂ) * V

/-- Both Cardano identities hold, including when either radicand is zero. -/
theorem signCorrected_pair (p q : ℂ) :
    signCorrectedV p q ^ 3 = radicandMinus p q ∧
      u p q * signCorrectedV p q = -p / 3 := by
  let U := principal (radicandPlus p q)
  let V := principal (radicandMinus p q)
  have hcube : (-p / 3) ^ 3 = (U * V) ^ 3 := by
    rw [mul_pow, principal_cube, principal_cube, radicands_product]
  obtain ⟨hpow, hprod⟩ := signPhase_corrects_cube hcube
  constructor
  · change (omega ^ (signPhase ((-p / 3) * conj (U * V)) : ℂ) * V) ^ 3 = _
    rw [mul_pow, hpow, one_mul, principal_cube]
  · change U * (omega ^ (signPhase ((-p / 3) * conj (U * V)) : ℂ) * V) = _
    rw [mul_left_comm]
    exact hprod

/-- Exact factorization for the sign version, preserving root multiplicities. -/
theorem signCorrected_depressed_factorization (p q x : ℂ) :
    (x - (u p q + signCorrectedV p q)) *
      (x - (omega * u p q + omega ^ 2 * signCorrectedV p q)) *
      (x - (omega ^ 2 * u p q + omega * signCorrectedV p q)) =
        x ^ 3 + p * x + q := by
  rw [factorization_identity, (signCorrected_pair p q).2, u_cube,
    (signCorrected_pair p q).1, radicands_sum]
  ring

/-- Any compatible pair of radicals solves the original cubic after the shift. -/
theorem cubic_formula_of_compatible_pair {a : ℂ} (ha : a ≠ 0) (b c d x U V : ℂ)
    (hsum : U ^ 3 + V ^ 3 = -depressedQ a b c d)
    (hprod : U * V = -depressedP a b c / 3) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = U + V - (b / a) / 3 ∨
      x = omega * U + omega ^ 2 * V - (b / a) / 3 ∨
      x = omega ^ 2 * U + omega * V - (b / a) / 3 := by
  have hmem := (mem_pairedRoots_iff (x := x + (b / a) / 3) hsum hprod).symm
  rw [depressed_shift] at hmem
  have hscale : a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
      a * x ^ 3 + b * x ^ 2 + c * x + d := by field_simp
  rw [← hscale, mul_eq_zero]
  simpa only [ha, false_or, pairedRoots, List.mem_cons, List.not_mem_nil, or_false,
    eq_sub_iff_add_eq] using hmem

/-- The round version. It uses `principal_arg_conventions` and rounds halfway
ties toward positive infinity, as stated in `round_half_tie_up`. -/
theorem cardano_formula_phaseCorrected_round {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let n := round ((3 * C.arg - A.arg - B.arg) / (2 * Real.pi))
    let u := principal A
    let v := ω ^ n * principal B
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  simpa only [phaseCorrectedCubicRoots, phaseCorrectedDepressedRoots, pairedRoots,
    u, phaseCorrectedV, phaseIndex, radicandPlus, radicandMinus, discriminant,
    depressedP, depressedQ, omega, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] using (mem_phaseCorrectedCubicRoots_iff ha b c d x).symm

/-- The floor version, equivalent to the round version by `round_eq`.
It uses `principal_arg_conventions`; the added `1/2` preserves upward ties. -/
theorem cardano_formula_phaseCorrected_floor {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let n := ⌊(3 * C.arg - A.arg - B.arg) / (2 * Real.pi) + 1 / 2⌋
    let u := principal A
    let v := ω ^ n * principal B
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  simpa only [phaseCorrectedCubicRoots, phaseCorrectedDepressedRoots, pairedRoots,
    u, phaseCorrectedV, phaseIndex_eq_floor, radicandPlus, radicandMinus, discriminant,
    depressedP, depressedQ, omega, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] using (mem_phaseCorrectedCubicRoots_iff ha b c d x).symm

/-- The sign version. The correction uses no argument function and requires no
convention for `arg 0`. The sign function has `sign 0 = 0`; the exponent `n` is
real-valued in the expression and is proved to be `0`, `1`, or `-1` on these inputs. -/
theorem cardano_formula_phaseCorrected_sign {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let u := principal A
    let w := principal B
    let Z := C * conj (u * w)
    let n : ℝ := (1 - Real.sign Z.re) * Real.sign Z.im / 2
    let v := ω ^ (n : ℂ) * w
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  let p := depressedP a b c
  let q := depressedQ a b c d
  have hpair := signCorrected_pair p q
  have hsum : u p q ^ 3 + signCorrectedV p q ^ 3 = -q := by
    rw [u_cube, hpair.1, radicands_sum]
  simpa only [p, q, u, signCorrectedV, signPhase, radicandPlus, radicandMinus,
    discriminant, depressedP, depressedQ, omega] using
    (cubic_formula_of_compatible_pair ha b c d x (u p q) (signCorrectedV p q) hsum hpair.2)

end RealCubeRoot.Cardano
