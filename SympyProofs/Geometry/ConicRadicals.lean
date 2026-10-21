module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Real.Sign
public import Mathlib.Tactic

/-!
# Explicit radical candidates for cubic and quartic equations

The lists use fixed complex square/cube roots and contain every root. The quartic
list deliberately includes extra candidates: this removes the usual division-by-zero
branch in Ferrari's formula. Geometry maps every candidate to a point on the curve,
so extra candidates cannot make the minimum smaller than the actual distance.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

def sqrtC (z : ℂ) : ℂ := z ^ (2⁻¹ : ℂ)
def cbrtC (z : ℂ) : ℂ := z ^ (3⁻¹ : ℂ)

@[simp] theorem sqrtC_sq (z : ℂ) : sqrtC z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide)

@[simp] theorem cbrtC_cube (z : ℂ) : cbrtC z ^ 3 = z :=
  Complex.cpow_nat_inv_pow z (by decide)

/-- A denominator which equals `z` off zero and equals one at zero. -/
def radicalDenom (z : ℂ) : ℂ := z + ((1 - Real.sign ‖z‖ : ℝ) : ℂ)

theorem radicalDenom_ne_zero (z : ℂ) : radicalDenom z ≠ 0 := by
  by_cases hz : z = 0
  · simp [radicalDenom, hz]
  · simpa [radicalDenom, Real.sign_of_pos (norm_pos_iff.mpr hz)] using hz

/-- Total reciprocal, written with an everywhere nonzero denominator. -/
def radicalInv (z : ℂ) : ℂ := (Real.sign ‖z‖ : ℂ) / radicalDenom z

@[simp] theorem radicalInv_eq (z : ℂ) : radicalInv z = z⁻¹ := by
  by_cases hz : z = 0
  · simp [radicalInv, radicalDenom, hz]
  · simp [radicalInv, radicalDenom, Real.sign_of_pos (norm_pos_iff.mpr hz), one_div]

/-- Cardano's cube-root choice, selecting the other radicand when the first is zero. -/
def cardanoU (p q : ℂ) : ℂ :=
  let d := sqrtC (q ^ 2 / 4 + p ^ 3 / 27)
  let a := cbrtC (-q / 2 + d)
  let b := cbrtC (-q / 2 - d)
  a + ((1 - Real.sign ‖a‖ : ℝ) : ℂ) * b

def depressedCubicRoot (p q : ℂ) : ℂ :=
  cardanoU p q - p / 3 * radicalInv (cardanoU p q)

private theorem cardano_identity (p q d u : ℂ)
    (hd : d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27)
    (hu : u ^ 3 = -q / 2 + d) (hne : u ≠ 0) :
    (u - p / 3 * u⁻¹) ^ 3 + p * (u - p / 3 * u⁻¹) + q = 0 := by
  have hpoly : u ^ 6 + q * u ^ 3 - p ^ 3 / 27 = 0 := by
    linear_combination (u ^ 3 + q / 2 + d) * hu + hd
  field_simp
  linear_combination 27 * hpoly

theorem depressedCubicRoot_spec (p q : ℂ) :
    depressedCubicRoot p q ^ 3 + p * depressedCubicRoot p q + q = 0 := by
  let d := sqrtC (q ^ 2 / 4 + p ^ 3 / 27)
  let a := cbrtC (-q / 2 + d)
  let b := cbrtC (-q / 2 - d)
  have hd : d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 := sqrtC_sq _
  have ha : a ^ 3 = -q / 2 + d := cbrtC_cube _
  have hb : b ^ 3 = -q / 2 - d := cbrtC_cube _
  change (a + ((1 - Real.sign ‖a‖ : ℝ) : ℂ) * b - p / 3 *
    radicalInv (a + ((1 - Real.sign ‖a‖ : ℝ) : ℂ) * b)) ^ 3 +
    p * (a + ((1 - Real.sign ‖a‖ : ℝ) : ℂ) * b - p / 3 *
    radicalInv (a + ((1 - Real.sign ‖a‖ : ℝ) : ℂ) * b)) + q = 0
  by_cases hane : a = 0
  · simp only [hane, norm_zero, Real.sign_zero, sub_zero, Complex.ofReal_one,
      one_mul, zero_add, radicalInv_eq]
    by_cases hbne : b = 0
    · have hq : q = 0 := by rw [hane] at ha; rw [hbne] at hb; linear_combination ha + hb
      simp [hbne, hq]
    · exact cardano_identity p q (-d) b (by simpa using hd)
        (by simpa only [sub_eq_add_neg] using hb) hbne
  · simp only [Real.sign_of_pos (norm_pos_iff.mpr hane), sub_self, Complex.ofReal_zero,
      zero_mul, add_zero, radicalInv_eq]
    exact cardano_identity p q d a hd ha hane

/-- The three Cardano/quadratic radical candidates, including repeated roots. -/
def cubicRadicals (p q : ℂ) : List ℂ :=
  let r := depressedCubicRoot p q
  let s := sqrtC (-3 * r ^ 2 - 4 * p)
  [r, (-r + s) / 2, (-r - s) / 2]

private theorem quadratic_cover (b c x : ℂ) (hx : x ^ 2 + b * x + c = 0) :
    x = (-b + sqrtC (b ^ 2 - 4 * c)) / 2 ∨
      x = (-b - sqrtC (b ^ 2 - 4 * c)) / 2 := by
  have h : (2 * x + b - sqrtC (b ^ 2 - 4 * c)) *
      (2 * x + b + sqrtC (b ^ 2 - 4 * c)) = 0 := by
    linear_combination 4 * hx - sqrtC_sq (b ^ 2 - 4 * c)
  rcases mul_eq_zero.mp h with h | h
  · left; linear_combination h / 2
  · right; linear_combination h / 2

theorem mem_cubicRadicals (p q x : ℂ) (hx : x ^ 3 + p * x + q = 0) :
    x ∈ cubicRadicals p q := by
  let r := depressedCubicRoot p q
  have hr : r ^ 3 + p * r + q = 0 := depressedCubicRoot_spec p q
  have hf : (x - r) * (x ^ 2 + r * x + (r ^ 2 + p)) = 0 := by
    linear_combination hx - hr
  simp only [cubicRadicals, List.mem_cons, List.not_mem_nil, or_false]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · have he : r ^ 2 - 4 * (r ^ 2 + p) = -3 * r ^ 2 - 4 * p := by ring
    exact Or.inr (by simpa only [he] using quadratic_cover r (r ^ 2 + p) x h)

/-- One root of a general monic cubic. -/
def monicCubicRoot (b c d : ℂ) : ℂ :=
  depressedCubicRoot (c - b ^ 2 / 3) (2 * b ^ 3 / 27 - b * c / 3 + d) - b / 3

theorem monicCubicRoot_spec (b c d : ℂ) :
    monicCubicRoot b c d ^ 3 + b * monicCubicRoot b c d ^ 2 +
      c * monicCubicRoot b c d + d = 0 := by
  dsimp [monicCubicRoot]
  linear_combination depressedCubicRoot_spec (c - b ^ 2 / 3)
    (2 * b ^ 3 / 27 - b * c / 3 + d)

/-- Ferrari candidates plus the biquadratic candidates. No root-selection branch is needed. -/
def depressedQuarticRadicals (p q r : ℂ) : List ℂ :=
  let z := monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2)
  let s := sqrtC z
  let u := sqrtC (-2 * p - z + 2 * q * radicalInv s)
  let v := sqrtC (-2 * p - z - 2 * q * radicalInv s)
  let w := sqrtC (p ^ 2 - 4 * r)
  [(-s + u) / 2, (-s - u) / 2, (s + v) / 2, (s - v) / 2,
    sqrtC ((-p + w) / 2), -sqrtC ((-p + w) / 2),
    sqrtC ((-p - w) / 2), -sqrtC ((-p - w) / 2)]

theorem mem_depressedQuarticRadicals (p q r x : ℂ)
    (hx : x ^ 4 + p * x ^ 2 + q * x + r = 0) :
    x ∈ depressedQuarticRadicals p q r := by
  let z := monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2)
  let s := sqrtC z
  have hz : z ^ 3 + 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z - q ^ 2 = 0 := by
    have h := monicCubicRoot_spec (2 * p) (p ^ 2 - 4 * r) (-q ^ 2)
    change z ^ 3 + 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z + (-q ^ 2) = 0 at h
    linear_combination h
  have hs : s ^ 2 = z := sqrtC_sq z
  simp only [depressedQuarticRadicals, List.mem_cons, List.not_mem_nil, or_false]
  by_cases hq : q = 0
  · have hquad : (x ^ 2) ^ 2 + p * x ^ 2 + r = 0 := by linear_combination hx - x * hq
    rcases quadratic_cover p r (x ^ 2) hquad with h | h
    · have hroots := eq_or_eq_neg_of_sq_eq_sq x (sqrtC ((-p + sqrtC (p ^ 2 - 4 * r)) / 2))
        (by simpa only [sqrtC_sq] using h)
      tauto
    · have hroots := eq_or_eq_neg_of_sq_eq_sq x (sqrtC ((-p - sqrtC (p ^ 2 - 4 * r)) / 2))
        (by simpa only [sqrtC_sq] using h)
      tauto
  · have hzne : z ≠ 0 := by
      intro h
      have : q ^ 2 = 0 := by simpa [h] using hz.symm
      exact (pow_ne_zero 2 hq) this
    have hsne : s ≠ 0 := fun h => hzne (by simpa [h] using hs.symm)
    have hf : (x ^ 2 + s * x + (p + z - q / s) / 2) *
        (x ^ 2 - s * x + (p + z + q / s) / 2) = 0 := by
      field_simp
      linear_combination 4 * s ^ 2 * hx + hz +
        ((p + z) ^ 2 - 4 * r - 4 * x ^ 2 * s ^ 2) * hs
    rcases mul_eq_zero.mp hf with h | h
    · have he : s ^ 2 - 4 * ((p + z - q / s) / 2) =
          -2 * p - z + 2 * q * radicalInv s := by
        simp only [radicalInv_eq, div_eq_mul_inv]
        linear_combination hs
      have hroots := quadratic_cover s ((p + z - q / s) / 2) x h
      rw [he] at hroots
      change x = (-s + _) / 2 ∨ x = (-s - _) / 2 ∨ _
      tauto
    · have he : (-s) ^ 2 - 4 * ((p + z + q / s) / 2) =
          -2 * p - z - 2 * q * radicalInv s := by
        simp only [radicalInv_eq, div_eq_mul_inv]
        linear_combination hs
      have hroots := quadratic_cover (-s) ((p + z + q / s) / 2) x
        (by linear_combination h)
      rw [he] at hroots
      simp only [neg_neg] at hroots
      change _ ∨ _ ∨ x = (s + _) / 2 ∨ x = (s - _) / 2 ∨ _
      tauto

/-- Explicit radical candidates for a monic quartic. -/
def quarticRadicals (b c d e : ℂ) : List ℂ :=
  let p := c - 3 * b ^ 2 / 8
  let q := b ^ 3 / 8 - b * c / 2 + d
  let r := -3 * b ^ 4 / 256 + b ^ 2 * c / 16 - b * d / 4 + e
  (depressedQuarticRadicals p q r).map (fun z => z - b / 4)

theorem mem_quarticRadicals (b c d e x : ℂ)
    (hx : x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0) :
    x ∈ quarticRadicals b c d e := by
  apply List.mem_map.mpr
  refine ⟨x + b / 4, mem_depressedQuarticRadicals _ _ _ _ ?_, by ring⟩
  linear_combination hx

/-- Real parameters covering the sparse quartic `A*t^4 + B*t^3 + D*t - A`.
The extra quadratic candidates cover vanishing leading coefficients. -/
def sparseQuarticRadicals (A B D : ℝ) : List ℝ :=
  let s := sqrtC (-(D : ℂ) * radicalInv B)
  [0, s.re, (-s).re] ++
    (quarticRadicals ((B : ℂ) * radicalInv A) 0 ((D : ℂ) * radicalInv A) (-1)).map Complex.re

theorem mem_sparseQuarticRadicals (A B D t : ℝ)
    (hn : A ≠ 0 ∨ B ≠ 0 ∨ D ≠ 0)
    (ht : A * t ^ 4 + B * t ^ 3 + D * t - A = 0) :
    t ∈ sparseQuarticRadicals A B D := by
  simp only [sparseQuarticRadicals, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  by_cases hA : A = 0
  · left
    have hf : t * (B * t ^ 2 + D) = 0 := by linear_combination ht - (t ^ 4 - 1) * hA
    rcases mul_eq_zero.mp hf with ht0 | hq
    · exact Or.inl ht0
    · have hB : B ≠ 0 := by
        intro hB
        have hD : D = 0 := by simpa [hB] using hq
        tauto
      have hc : (t : ℂ) ^ 2 = -(D : ℂ) * radicalInv B := by
        simp only [radicalInv_eq]
        have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB
        field_simp
        exact_mod_cast (show t ^ 2 * B = -D by linarith)
      have he := eq_or_eq_neg_of_sq_eq_sq (t : ℂ)
        (sqrtC (-(D : ℂ) * radicalInv B)) (by simpa only [sqrtC_sq] using hc)
      exact Or.inr (he.imp (fun h => by simpa using congrArg Complex.re h)
        (fun h => by simpa using congrArg Complex.re h))
  · right
    apply List.mem_map.mpr
    refine ⟨(t : ℂ), mem_quarticRadicals _ _ _ _ _ ?_, by simp⟩
    simp only [radicalInv_eq, zero_mul, add_zero]
    have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA
    have htc : (A : ℂ) * (t : ℂ) ^ 4 + (B : ℂ) * (t : ℂ) ^ 3 +
        (D : ℂ) * (t : ℂ) - (A : ℂ) = 0 := by exact_mod_cast ht
    field_simp
    linear_combination htc

end
end SympyGeometry
