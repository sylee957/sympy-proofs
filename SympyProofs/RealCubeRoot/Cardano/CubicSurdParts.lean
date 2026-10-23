module

public import SympyProofs.RealCubeRoot.Cardano.CubicSurd

/-!
# Cardano's formula with cubic surds and explicit real and imaginary parts

Expand the factors involving `omega` into real arithmetic. For nonnegative
discriminant the radicals use `realCubicSurd`; for nonpositive discriminant
all three roots are real and can be listed in ascending order.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

private theorem side_conj (S : ℂ → ℂ) (hS : S = cubicSurdLeft ∨ S = cubicSurdRight) :
    ∀ z, S (conj z) = conj (S z) := by
  rcases hS with rfl | rfl
  · exact cubicSurdLeft_conj
  · exact cubicSurdRight_conj

/-- Expand the three Cardano values into real and imaginary coordinates.
The only hypothesis is that the sum of the two chosen radicals is real. -/
theorem pairedRoots_eq_re_im (u v : ℂ) (him : (u + v).im = 0) :
    let t := u.re + v.re
    let r := Real.sqrt 3 / 2 * (u.im - v.im)
    let j := Real.sqrt 3 / 2 * (u.re - v.re)
    pairedRoots u v = [(t : ℂ), ⟨-t / 2 - r, j⟩, ⟨-t / 2 + r, -j⟩] := by
  have h0 : u + v = ((u.re + v.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have h1 : omega * u + omega ^ 2 * v =
      (⟨-(u.re + v.re) / 2 - Real.sqrt 3 / 2 * (u.im - v.im),
        Real.sqrt 3 / 2 * (u.re - v.re)⟩ : ℂ) := by
    rw [omega_sq]
    apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [show u.im + v.im = 0 from him]
  have h2 : omega ^ 2 * u + omega * v =
      (⟨-(u.re + v.re) / 2 + Real.sqrt 3 / 2 * (u.im - v.im),
        -(Real.sqrt 3 / 2 * (u.re - v.re))⟩ : ℂ) := by
    rw [omega_sq]
    apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [show u.im + v.im = 0 from him]
  simp only [pairedRoots, h0, h1, h2]

/-- The symmetric formula with `omega` eliminated. Every coordinate is a real
expression, and the first solution has imaginary part exactly zero. -/
theorem cardano_formula_cubicSurd_re_im (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight)
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let s := Complex.sqrt (Δ : ℂ)
    let u := S (-(q : ℂ) / 2 + s)
    let v := S (-(q : ℂ) / 2 - s)
    let t := u.re + v.re
    let r := Real.sqrt 3 / 2 * (u.im - v.im)
    let j := Real.sqrt 3 / 2 * (u.re - v.re)
    let shift : ℝ := (b / a) / 3
    let x₀ : ℂ := ⟨t - shift, 0⟩
    let x₁ : ℂ := ⟨-t / 2 - r - shift, j⟩
    let x₂ : ℂ := ⟨-t / 2 + r - shift, -j⟩
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  have hcube : ∀ z, S z ^ 3 = z := by
    rcases hS with rfl | rfl
    · exact cubicSurdLeft_cube
    · exact cubicSurdRight_cube
  have him (p q : ℝ) :
      (S (radicandPlus (p : ℂ) q) + S (radicandMinus (p : ℂ) q)).im = 0 :=
    Complex.conj_eq_iff_im.mp (direct_pair_conj_of_conj S (side_conj S hS) p q).1
  have hparts (p q : ℝ) := pairedRoots_eq_re_im
    (S (radicandPlus (p : ℂ) q)) (S (radicandMinus (p : ℂ) q)) (him p q)
  have h := (symmetric_cubic_roots_iff_of_cube_conj S hcube (side_conj S hS) ha b c d x).symm
  simp only [hparts, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h
  have hsub (r i s : ℝ) : (⟨r, i⟩ : ℂ) - (s : ℂ) = ⟨r - s, i⟩ := by
    apply Complex.ext <;> simp
  have hshift : ((b / a : ℝ) : ℂ) / 3 = (((b / a) / 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  simpa only [radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant,
    hshift, ← Complex.ofReal_sub, hsub, Complex.ofReal_re, Complex.ofReal_im] using h

private theorem sqrt_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    Complex.sqrt (r : ℂ) = (Real.sqrt r : ℂ) := by
  exact Complex.sqrt_of_nonneg (by exact_mod_cast hr)

/-- For nonnegative discriminant, all radicals are real cubic surds. The
other two solutions have the same real part and opposite imaginary parts. -/
theorem cardano_formula_cubicSurd_of_discriminant_nonneg
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    0 ≤ Δ →
    let s := Real.sqrt Δ
    let u := realCubicSurd (-q / 2 + s)
    let v := realCubicSurd (-q / 2 - s)
    let t := u + v
    let j := Real.sqrt 3 / 2 * (u - v)
    let shift : ℝ := (b / a) / 3
    let x₀ : ℂ := ⟨t - shift, 0⟩
    let x₁ : ℂ := ⟨-t / 2 - shift, j⟩
    let x₂ : ℂ := ⟨-t / 2 - shift, -j⟩
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  dsimp only
  intro hD
  have h := cardano_formula_cubicSurd_re_im cubicSurdRight (Or.inr rfl) ha b c d x
  have hplus (q s : ℝ) : -(q : ℂ) / 2 + (s : ℂ) = ((-q / 2 + s : ℝ) : ℂ) := by
    push_cast
    rfl
  have hminus (q s : ℝ) : -(q : ℂ) / 2 - (s : ℂ) = ((-q / 2 - s : ℝ) : ℂ) := by
    push_cast
    rfl
  simpa only [sqrt_ofReal_of_nonneg hD, hplus, hminus, cubicSurdRight_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, sub_self, mul_zero, sub_zero, add_zero] using h

private theorem pair_conj_of_nonpos (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight) (q Δ : ℝ) (hD : Δ ≤ 0) :
    S (-(q : ℂ) / 2 - Complex.sqrt (Δ : ℂ)) =
      conj (S (-(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ))) := by
  have hsre : (Complex.sqrt (Δ : ℂ)).re = 0 := by
    rw [Complex.re_sqrt_ofReal, Real.sqrt_eq_zero_of_nonpos hD]
  have hs : conj (Complex.sqrt (Δ : ℂ)) = -Complex.sqrt (Δ : ℂ) := by
    apply Complex.ext <;> simp [hsre]
  rw [← side_conj S hS]
  congr 1
  simp only [map_add, map_div₀, map_neg, conj_ofReal, hs,
    show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_eq_add_neg]

/-- For nonpositive discriminant, the real and imaginary parts of one surd
give all three real roots, without any factors involving `omega`. -/
theorem cardano_formula_cubicSurd_of_discriminant_nonpos (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight)
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    Δ ≤ 0 →
    let w := S (-(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ))
    let A := w.re
    let B := w.im
    let shift : ℝ := (b / a) / 3
    let r₀ := 2 * A - shift
    let r₁ := -A - Real.sqrt 3 * B - shift
    let r₂ := -A + Real.sqrt 3 * B - shift
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = (r₀ : ℂ) ∨ x = (r₁ : ℂ) ∨ x = (r₂ : ℂ) := by
  dsimp only
  intro hD
  have h := cardano_formula_cubicSurd_re_im S hS ha b c d x
  simp only [pair_conj_of_nonpos S hS _ _ hD, Complex.conj_re, Complex.conj_im,
    sub_self, mul_zero, neg_zero] at h
  have hdouble (r : ℝ) : r + r = 2 * r := by ring
  have hhalf (r : ℝ) : -(2 * r) / 2 = -r := by ring
  have him (i : ℝ) : Real.sqrt 3 / 2 * (i - -i) = Real.sqrt 3 * i := by ring
  have hmk (r : ℝ) : (⟨r, 0⟩ : ℂ) = (r : ℂ) := by
    apply Complex.ext <;> simp
  simpa only [hhalf, hdouble, him, hmk] using h

private theorem sort_three (r₀ r₁ r₂ : ℝ) :
    let lo := min r₀ (min r₁ r₂)
    let hi := max r₀ (max r₁ r₂)
    let mid := r₀ + r₁ + r₂ - lo - hi
    lo ≤ mid ∧ mid ≤ hi ∧
      ∀ x : ℝ, (x = r₀ ∨ x = r₁ ∨ x = r₂) ↔ (x = lo ∨ x = mid ∨ x = hi) := by
  dsimp only
  rcases le_total r₀ r₁ with h01 | h10 <;>
    rcases le_total r₁ r₂ with h12 | h21 <;>
    rcases le_total r₀ r₂ with h02 | h20
  all_goals
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring_nf
    grind

/-- All real roots in ascending order when the discriminant is nonpositive.
The min/max expressions also handle repeated roots and either cut convention. -/
theorem cardano_formula_cubicSurd_sorted (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight)
    {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (x : ℝ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    Δ ≤ 0 →
    let w := S (-(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ))
    let A := w.re
    let B := w.im
    let shift : ℝ := (b / a) / 3
    let r₀ := 2 * A - shift
    let r₁ := -A - Real.sqrt 3 * B - shift
    let r₂ := -A + Real.sqrt 3 * B - shift
    let lo := min r₀ (min r₁ r₂)
    let hi := max r₀ (max r₁ r₂)
    let mid := r₀ + r₁ + r₂ - lo - hi
    lo ≤ mid ∧ mid ≤ hi ∧
      (a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = lo ∨ x = mid ∨ x = hi) := by
  dsimp only
  intro hD
  have h := cardano_formula_cubicSurd_of_discriminant_nonpos S hS ha b c d (x : ℂ) hD
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_zero, Complex.ofReal_inj] at h
  refine ⟨(sort_three _ _ _).1, (sort_three _ _ _).2.1, ?_⟩
  exact h.trans ((sort_three _ _ _).2.2 x)

end RealCubeRoot.Cardano
