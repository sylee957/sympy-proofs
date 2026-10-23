module

public import SympyProofs.RealCubeRoot.Principal
public import SympyProofs.RealCubeRoot.RealCubicSurd

/-!
# A modified principal cube root expressed without conditionals

With `η = (1 + i * sqrt(3)) / 2`, define
`modifiedPrincipal z = η * principal z + conj η * conj (principal (conj z))`.
It equals the principal cube root off the negative real axis, and the real
cubic surd on every real input. Its cube equation and conjugation identity
hold on all of `ℂ`, including zero.

This branch differs from `cubicSurdLeft` and `cubicSurdRight`: it retains the
principal values at every nonreal input. The absence of conditionals in its
expression does not assert global continuity or analyticity.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex
open scoped ComplexConjugate

/-- A real-compatible cube root using only principal cube roots, conjugation,
and arithmetic, with no conditionals or variable denominators. -/
def modifiedPrincipal (z : ℂ) : ℂ :=
  let η : ℂ := (1 + (Real.sqrt 3 : ℂ) * I) / 2
  η * principal z + conj η * conj (principal (conj z))

@[simp] theorem modifiedPrincipal_zero : modifiedPrincipal 0 = 0 := by
  simp [modifiedPrincipal, principal]

@[simp] theorem modifiedPrincipal_conj (z : ℂ) :
    modifiedPrincipal (conj z) = conj (modifiedPrincipal z) := by
  simp only [modifiedPrincipal, map_add, map_mul, conj_conj]
  ring

/-- Away from the nonpositive real axis, the two principal-root terms combine
to the principal cube root itself. -/
theorem modifiedPrincipal_eq_principal {z : ℂ} (hz : z ∈ slitPlane) :
    modifiedPrincipal z = principal z := by
  rw [modifiedPrincipal, principal_conj_of_mem_slitPlane hz, conj_conj]
  simp only [map_div₀, map_add, map_one, map_mul, conj_ofReal, conj_I,
    show conj (2 : ℂ) = 2 from conj_ofReal 2]
  ring

private theorem modifiedPrincipal_ofReal_neg {x : ℝ} (hx : x < 0) :
    modifiedPrincipal (x : ℂ) = (realCubicSurd x : ℂ) := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp only [modifiedPrincipal, conj_ofReal, principal_ofReal_of_neg hx,
    map_mul, map_div₀, map_add, map_one, conj_I,
    show conj (2 : ℂ) = 2 from conj_ofReal 2,
    realCubicSurd, hx, ↓reduceIte, Complex.ofReal_neg]
  calc
    _ = (((-x) ^ (3⁻¹ : ℝ) : ℝ) : ℂ) *
      (1 + (Real.sqrt 3 : ℂ) ^ 2 * I ^ 2) / 2 := by ring
    _ = _ := by rw [hs, I_sq]; ring

/-- Every real input is sent to its unique real cube root. -/
@[simp] theorem modifiedPrincipal_ofReal (x : ℝ) :
    modifiedPrincipal (x : ℂ) = (realCubicSurd x : ℂ) := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · exact modifiedPrincipal_ofReal_neg hn
  · simp
  · rw [modifiedPrincipal_eq_principal (Or.inl hp), principal_ofReal_of_nonneg hp.le]
    simp [realCubicSurd, not_lt.mpr hp.le]

/-- The cube equation holds everywhere, including the branch cut and zero. -/
@[simp] theorem modifiedPrincipal_cube (z : ℂ) : modifiedPrincipal z ^ 3 = z := by
  by_cases hz : z.im = 0
  · have hreal : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hz]
    rw [← hreal, modifiedPrincipal_ofReal, ← Complex.ofReal_pow, realCubicSurd_cube]
  · rw [modifiedPrincipal_eq_principal (Or.inr hz), principal_cube]

/-- Realness is both preserved and reflected. -/
theorem modifiedPrincipal_im_eq_zero_iff (z : ℂ) :
    (modifiedPrincipal z).im = 0 ↔ z.im = 0 := by
  constructor
  · intro h
    have ht := Complex.conj_eq_iff_im.mpr h
    apply Complex.conj_eq_iff_im.mp
    calc
      conj z = conj (modifiedPrincipal z ^ 3) := by rw [modifiedPrincipal_cube]
      _ = modifiedPrincipal z ^ 3 := by rw [map_pow, ht]
      _ = z := modifiedPrincipal_cube z
  · intro h
    have hreal : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [h]
    rw [← hreal, modifiedPrincipal_ofReal, Complex.ofReal_im]

/-- When conjugating the two inputs preserves their principal-root sum, the
sum of the modified roots is `re W - sqrt(3) * im W`. The individual inputs
need not be real. -/
theorem modifiedPrincipal_add_eq_re_im {z w : ℂ}
    (h : principal (conj z) + principal (conj w) = principal z + principal w) :
    modifiedPrincipal z + modifiedPrincipal w =
      (((principal z + principal w).re -
        Real.sqrt 3 * (principal z + principal w).im : ℝ) : ℂ) := by
  let η : ℂ := (1 + (Real.sqrt 3 : ℂ) * I) / 2
  have hsum : modifiedPrincipal z + modifiedPrincipal w =
      η * (principal z + principal w) + conj η * conj (principal z + principal w) := by
    calc
      _ = η * (principal z + principal w) +
          conj η * conj (principal (conj z) + principal (conj w)) := by
        simp only [modifiedPrincipal, map_add, η]
        ring
      _ = _ := by rw [h]
  rw [hsum]
  apply Complex.ext <;>
    simp [η, Complex.mul_re, Complex.mul_im,
      show conj (2 : ℂ) = 2 from conj_ofReal 2] <;> ring

end RealCubeRoot
