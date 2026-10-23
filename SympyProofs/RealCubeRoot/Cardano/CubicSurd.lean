module

public import SympyProofs.RealCubeRoot.Cardano.Principal
public import SympyProofs.RealCubeRoot.Extensions

/-!
# Cardano's formula with cubic surds

For real `p,q`, choose `S = cubicSurdLeft` or `S = cubicSurdRight` and use
`S(-q/2 + sqrt(D))` and `S(-q/2 - sqrt(D))`. Their product is `-p/3`, their sum
is real, and no quotient correction is required. This includes negative, zero,
and positive `D`, as well as radicands on the imaginary-axis cut.

This direct surd pair gives the same solutions as the principal-root formula,
possibly in a different order. When `D <= 0`, all three solutions are real.
A real-valued solution is also defined for every real cubic with nonzero
leading coefficient.
See `cardano_formula_cubicSurd` for the equation and the direct two-surd
formula with either choice, using `let` bindings for every intermediate quantity.
The `surdU`/`surdV` definitions use the right side.
See `CubicSurdParts.lean` for explicit real/imaginary coordinates, real cubic
surds when the discriminant is nonnegative, and sorted real solutions when it
is nonpositive.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

def realDiscriminant (p q : ℝ) : ℝ := q ^ 2 / 4 + p ^ 3 / 27

theorem discriminant_ofReal (p q : ℝ) :
    discriminant (p : ℂ) q = (realDiscriminant p q : ℂ) := by
  simp [discriminant, realDiscriminant, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow]

/-- The direct first surd for real coefficients; its value can be complex. -/
def surdU (p q : ℝ) : ℂ := cubicSurdRight (radicandPlus (p : ℂ) q)

/-- The direct second surd for real coefficients, without a quotient correction. -/
def surdV (p q : ℝ) : ℂ := cubicSurdRight (radicandMinus (p : ℂ) q)

@[simp] theorem surdU_cube (p q : ℝ) : surdU p q ^ 3 = radicandPlus (p : ℂ) q :=
  cubicSurdRight_cube _

@[simp] theorem surdV_cube (p q : ℝ) : surdV p q ^ 3 = radicandMinus (p : ℂ) q :=
  cubicSurdRight_cube _

/-- For real coefficients, a conjugation-preserving function sends the two
radicands to values whose sum and product are real. -/
theorem direct_pair_conj_of_conj (S : ℂ → ℂ)
    (hconj : ∀ z, S (conj z) = conj (S z)) (p q : ℝ) :
    conj (S (radicandPlus (p : ℂ) q) + S (radicandMinus (p : ℂ) q)) =
      S (radicandPlus (p : ℂ) q) + S (radicandMinus (p : ℂ) q) ∧
    conj (S (radicandPlus (p : ℂ) q) * S (radicandMinus (p : ℂ) q)) =
      S (radicandPlus (p : ℂ) q) * S (radicandMinus (p : ℂ) q) := by
  let s := Complex.sqrt (discriminant (p : ℂ) q)
  have hs : conj s ^ 2 = s ^ 2 := by
    rw [← map_pow]
    change conj (Complex.sqrt (discriminant (p : ℂ) q) ^ 2) =
      Complex.sqrt (discriminant (p : ℂ) q) ^ 2
    rw [sqrt_sq, discriminant_ofReal, conj_ofReal]
  have hcases := eq_or_eq_neg_of_sq_eq_sq (conj s) s hs
  change conj (S (-((q : ℂ)) / 2 + s) + S (-((q : ℂ)) / 2 - s)) = _ ∧
    conj (S (-((q : ℂ)) / 2 + s) * S (-((q : ℂ)) / 2 - s)) = _
  rcases hcases with hs | hs
  · have ha : conj (-((q : ℂ)) / 2 + s) = -((q : ℂ)) / 2 + s := by
      simp only [map_add, map_div₀, map_neg, conj_ofReal, hs,
        show conj (2 : ℂ) = 2 from conj_ofReal 2]
    have hb : conj (-((q : ℂ)) / 2 - s) = -((q : ℂ)) / 2 - s := by
      simp only [map_sub, map_div₀, map_neg, conj_ofReal, hs,
        show conj (2 : ℂ) = 2 from conj_ofReal 2]
    constructor <;> simp only [map_add, map_mul, ← hconj, ha, hb] <;> rfl
  · have ha : conj (-((q : ℂ)) / 2 + s) = -((q : ℂ)) / 2 - s := by
      simp only [map_add, map_div₀, map_neg, conj_ofReal, hs,
        show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_eq_add_neg]
    have hb : conj (-((q : ℂ)) / 2 - s) = -((q : ℂ)) / 2 + s := by
      simp only [map_sub, map_div₀, map_neg, conj_ofReal, hs,
        show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_neg_eq_add]
    constructor <;> simp only [map_add, map_mul, ← hconj, ha, hb]
    · exact add_comm _ _
    · exact mul_comm _ _

/-- The sum and product of the directly selected right-side cube roots are real. -/
theorem direct_pair_conj (p q : ℝ) :
    conj (surdU p q + surdV p q) = surdU p q + surdV p q ∧
    conj (surdU p q * surdV p q) = surdU p q * surdV p q :=
  direct_pair_conj_of_conj cubicSurdRight cubicSurdRight_conj p q

/-- Any total cube root commuting with conjugation automatically gives the
compatible pair required by Cardano for real coefficients. -/
theorem direct_pair_product_of_cube_conj (S : ℂ → ℂ)
    (hcube : ∀ z, S z ^ 3 = z) (hconj : ∀ z, S (conj z) = conj (S z))
    (p q : ℝ) :
    S (radicandPlus (p : ℂ) q) * S (radicandMinus (p : ℂ) q) = -(p : ℂ) / 3 := by
  let t := S (radicandPlus (p : ℂ) q) * S (radicandMinus (p : ℂ) q)
  have hcube : t ^ 3 = (-(p : ℂ) / 3) ^ 3 := by
    rw [show t ^ 3 = S (radicandPlus (p : ℂ) q) ^ 3 *
      S (radicandMinus (p : ℂ) q) ^ 3 from mul_pow _ _ _, hcube, hcube, radicands_product]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp (direct_pair_conj_of_conj S hconj p q).2
  have hreal : r ^ 3 = (-p / 3) ^ 3 := by
    rw [show t = (r : ℂ) from hr] at hcube
    exact_mod_cast hcube
  have heq : r = -p / 3 := (show Odd (3 : ℕ) by decide).pow_injective hreal
  rw [hr, heq]
  push_cast
  rfl

/-- For the right-side surd, conjugation symmetry forces the required pairing. -/
theorem direct_pair_product (p q : ℝ) :
    surdU p q * surdV p q = -(p : ℂ) / 3 :=
  direct_pair_product_of_cube_conj cubicSurdRight cubicSurdRight_cube cubicSurdRight_conj p q

/-- All three roots obtained from the direct surd pair for real coefficients. -/
def surdDepressedRoots (p q : ℝ) : List ℂ := pairedRoots (surdU p q) (surdV p q)

theorem mem_surdDepressedRoots_iff (p q : ℝ) (x : ℂ) :
    x ∈ surdDepressedRoots p q ↔ x ^ 3 + (p : ℂ) * x + q = 0 := by
  apply mem_pairedRoots_iff
  · rw [surdU_cube, surdV_cube, radicands_sum]
  · exact direct_pair_product p q

/-- The principal and surd formulas have the same solutions; their list order may differ. -/
theorem mem_surdDepressedRoots_iff_mem_depressedRoots (p q : ℝ) (x : ℂ) :
    x ∈ surdDepressedRoots p q ↔ x ∈ depressedRoots (p : ℂ) q :=
  (mem_surdDepressedRoots_iff p q x).trans (mem_depressedRoots_iff (p : ℂ) q x).symm

/-- The symmetric Cardano expression is a root for every real `p,q`. -/
theorem symmetric_root_spec (p q : ℝ) :
    (cubicSurdRight (radicandPlus (p : ℂ) q) + cubicSurdRight (radicandMinus (p : ℂ) q)) ^ 3 +
      (p : ℂ) * (cubicSurdRight (radicandPlus (p : ℂ) q) + cubicSurdRight (radicandMinus (p : ℂ) q)) + q = 0 := by
  exact (mem_surdDepressedRoots_iff p q _).mp
    (by simp [surdDepressedRoots, pairedRoots, surdU, surdV])

theorem symmetric_root_isReal (p q : ℝ) :
    (cubicSurdRight (radicandPlus (p : ℂ) q) + cubicSurdRight (radicandMinus (p : ℂ) q)).im = 0 :=
  Complex.conj_eq_iff_im.mp (direct_pair_conj p q).1

theorem surdV_eq_conj_surdU_of_discriminant_nonpos (p q : ℝ)
    (hD : realDiscriminant p q ≤ 0) : surdV p q = conj (surdU p q) := by
  have hsre : (Complex.sqrt (discriminant (p : ℂ) q)).re = 0 := by
    rw [discriminant_ofReal, Complex.re_sqrt_ofReal, Real.sqrt_eq_zero_of_nonpos hD]
  have hs : conj (Complex.sqrt (discriminant (p : ℂ) q)) =
      -Complex.sqrt (discriminant (p : ℂ) q) := by
    apply Complex.ext <;> simp [hsre]
  rw [surdV, surdU, ← cubicSurdRight_conj]
  congr 1
  simp only [radicandPlus, radicandMinus, map_add, map_div₀, map_neg, conj_ofReal,
    hs, show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_eq_add_neg]

/-- In the casus irreducibilis regime (and its zero-discriminant boundary), all
three Cardano values are real, without evaluating their real and imaginary parts. -/
theorem all_surd_roots_real_of_discriminant_nonpos (p q : ℝ)
    (hD : realDiscriminant p q ≤ 0) {x : ℂ} (hx : x ∈ surdDepressedRoots p q) :
    x.im = 0 := by
  have hv := surdV_eq_conj_surdU_of_discriminant_nonpos p q hD
  have hw : conj (omega ^ 2) = omega := by
    simpa only [map_star, starRingEnd_apply, star_star] using
      (congrArg conj omega_conj).symm
  apply Complex.conj_eq_iff_im.mp
  simp only [surdDepressedRoots, pairedRoots, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact (direct_pair_conj p q).1
  · rw [hv]
    simp only [map_add, map_mul, omega_conj, hw, conj_conj]
    exact add_comm _ _
  · rw [hv]
    simp only [map_add, map_mul, omega_conj, hw, conj_conj]
    exact add_comm _ _

/-- The principal-root formula also gives only real roots in this regime. -/
theorem all_roots_real_of_discriminant_nonpos (p q : ℝ)
    (hD : realDiscriminant p q ≤ 0) {x : ℂ} (hx : x ∈ depressedRoots (p : ℂ) q) :
    x.im = 0 :=
  all_surd_roots_real_of_discriminant_nonpos p q hD
    ((mem_surdDepressedRoots_iff_mem_depressedRoots p q x).mpr hx)

/-- The symmetric complex expression, viewed as a real number. -/
def realDepressedRoot (p q : ℝ) : ℝ :=
  (cubicSurdRight (radicandPlus (p : ℂ) q) + cubicSurdRight (radicandMinus (p : ℂ) q)).re

theorem realDepressedRoot_coe (p q : ℝ) :
    (realDepressedRoot p q : ℂ) =
      cubicSurdRight (radicandPlus (p : ℂ) q) + cubicSurdRight (radicandMinus (p : ℂ) q) :=
  Complex.conj_eq_iff_re.mp (direct_pair_conj p q).1

theorem realDepressedRoot_spec (p q : ℝ) :
    realDepressedRoot p q ^ 3 + p * realDepressedRoot p q + q = 0 := by
  have h := symmetric_root_spec p q
  rw [← realDepressedRoot_coe] at h
  exact_mod_cast h

theorem depressedP_ofReal (a b c : ℝ) :
    depressedP (a : ℂ) b c = (c / a - (b / a) ^ 2 / 3 : ℝ) := by
  push_cast
  rfl

theorem depressedQ_ofReal (a b c d : ℝ) :
    depressedQ (a : ℂ) b c d =
      (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a : ℝ) := by
  push_cast
  rfl

/-- The symmetric formula is valid for any total cube root commuting with
conjugation, in particular for either one-sided extension. -/
theorem symmetric_cubic_roots_iff_of_cube_conj (S : ℂ → ℂ)
    (hcube : ∀ z, S z ^ 3 = z) (hconj : ∀ z, S (conj z) = conj (S z))
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    x ∈ (pairedRoots (S (radicandPlus (p : ℂ) q))
      (S (radicandMinus (p : ℂ) q))).map
        (fun z => z - ((b / a : ℝ) : ℂ) / 3) ↔
      (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 := by
  have hroots (p q : ℝ) (y : ℂ) :
      y ∈ pairedRoots (S (radicandPlus (p : ℂ) q)) (S (radicandMinus (p : ℂ) q)) ↔
        y ∈ depressedRoots (p : ℂ) q :=
    (mem_pairedRoots_iff (by rw [hcube, hcube, radicands_sum])
      (direct_pair_product_of_cube_conj S hcube hconj p q)).trans
        (mem_depressedRoots_iff (p : ℂ) q y).symm
  have h := mem_cubicRoots_iff (a := (a : ℂ)) (by exact_mod_cast ha)
    (b : ℂ) c d x
  simpa only [cubicRoots, depressedP_ofReal, depressedQ_ofReal,
    List.mem_map, ← hroots, Complex.ofReal_div] using h

/-- The right-side symmetric formula gives exactly all complex solutions of a
real cubic, including its nonreal roots when those occur. -/
theorem symmetric_cubic_roots_iff {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    x ∈ (pairedRoots (cubicSurdRight (radicandPlus (p : ℂ) q))
      (cubicSurdRight (radicandMinus (p : ℂ) q))).map
        (fun z => z - ((b / a : ℝ) : ℂ) / 3) ↔
      (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 :=
  symmetric_cubic_roots_iff_of_cube_conj cubicSurdRight
    cubicSurdRight_cube cubicSurdRight_conj ha b c d x

/-- Choose either the left or the right extension and use that same function
for both radicals. Either choice gives the complete solution set. -/
theorem cardano_formula_cubicSurd (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight)
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let s := Complex.sqrt (Δ : ℂ)
    let u := S (-(q : ℂ) / 2 + s)
    let v := S (-(q : ℂ) / 2 - s)
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift : ℝ := (b / a) / 3
    let x₀ := u + v - (shift : ℂ)
    let x₁ := ω * u + ω ^ 2 * v - (shift : ℂ)
    let x₂ := ω ^ 2 * u + ω * v - (shift : ℂ)
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  have hcube : ∀ z, S z ^ 3 = z := by
    rcases hS with rfl | rfl
    · exact cubicSurdLeft_cube
    · exact cubicSurdRight_cube
  have hconj : ∀ z, S (conj z) = conj (S z) := by
    rcases hS with rfl | rfl
    · exact cubicSurdLeft_conj
    · exact cubicSurdRight_conj
  simpa only [pairedRoots, radicandPlus, radicandMinus, discriminant_ofReal,
    realDiscriminant, omega, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, Complex.ofReal_div, Complex.ofReal_ofNat] using
    (symmetric_cubic_roots_iff_of_cube_conj S hcube hconj ha b c d x).symm

/-- A real solution of an arbitrary real cubic, obtained by shifting Cardano's root. -/
def realCubicRoot (a b c d : ℝ) : ℝ :=
  realDepressedRoot (c / a - (b / a) ^ 2 / 3)
    (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a) - (b / a) / 3

theorem realCubicRoot_spec {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) :
    a * realCubicRoot a b c d ^ 3 + b * realCubicRoot a b c d ^ 2 +
      c * realCubicRoot a b c d + d = 0 := by
  let r := realDepressedRoot (c / a - (b / a) ^ 2 / 3)
    (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a)
  have hr := realDepressedRoot_spec (c / a - (b / a) ^ 2 / 3)
    (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a)
  change r ^ 3 + _ * r + _ = 0 at hr
  have hnorm : (r - (b / a) / 3) ^ 3 + (b / a) * (r - (b / a) / 3) ^ 2 +
      (c / a) * (r - (b / a) / 3) + d / a = 0 := by
    linear_combination hr
  have hscale : a * ((r - (b / a) / 3) ^ 3 + (b / a) * (r - (b / a) / 3) ^ 2 +
      (c / a) * (r - (b / a) / 3) + d / a) =
      a * (r - (b / a) / 3) ^ 3 + b * (r - (b / a) / 3) ^ 2 +
        c * (r - (b / a) / 3) + d := by
    field_simp
  change a * (r - (b / a) / 3) ^ 3 + b * (r - (b / a) / 3) ^ 2 +
    c * (r - (b / a) / 3) + d = 0
  rw [← hscale, hnorm, mul_zero]

end RealCubeRoot.Cardano
