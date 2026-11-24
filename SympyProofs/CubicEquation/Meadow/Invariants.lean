module

public import SympyProofs.CubicEquation.Meadow.Formula

/-!
# Meadow cubic formula in terms of D₀ and D₁

For a monic cubic x³ + ax² + bx + c, let D₀ = a² - 3b and
D₁ = 2a³ - 9ab + 27c. The first cube-root radicand is
R = (D₁ + √(D₁² - 4D₀³))/2. The other radicand is D₁ - R.
With meadow inverse, R + (1 - R*R⁻¹)*D₁ selects the other radicand when R
vanishes. The roots are indexed by 1, ω, and ω² in that order.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot

/-- The D₀,D₁ formula for x³ + ax² + bx + c, using principal radicals. -/
def meadowCubicRootsViaInvariants (a b c : ℂ) : CardanoRoots :=
  let D₀ := a ^ 2 - 3 * b
  let D₁ := 2 * a ^ 3 - 9 * a * b + 27 * c
  let R := (D₁ + Complex.sqrt (D₁ ^ 2 - 4 * D₀ ^ 3)) / 2
  let C := (R + (1 - R * R⁻¹) * D₁) ^ (3⁻¹ : ℂ)
  let root (ζ : ℂ) := -(a + ζ * C + D₀ / (ζ * C)) / 3
  ⟨root 1, root omega, root (omega ^ 2)⟩

/-- Correctness with multiplicities, including a zero radicand and repeated roots. -/
theorem monicCubic_roots_meadowInvariants (a b c : ℂ) :
    let r := meadowCubicRootsViaInvariants a b c
    (monicCubic a b c).roots = {r.x₀, r.x₁, r.x₂} := by
  let D₀ := a ^ 2 - 3 * b
  let D₁ := 2 * a ^ 3 - 9 * a * b + 27 * c
  let R := (D₁ + Complex.sqrt (D₁ ^ 2 - 4 * D₀ ^ 3)) / 2
  have hR : R * (D₁ - R) = D₀ ^ 3 := by
    dsimp only [R]
    linear_combination -(1 / 4 : ℂ) * sqrt_sq (D₁ ^ 2 - 4 * D₀ ^ 3)
  let C := principal (R + (1 - R * R⁻¹) * D₁)
  let D := D₀ * C⁻¹
  obtain ⟨hs, hp⟩ : C ^ 3 + D ^ 3 = D₁ ∧ C * D = D₀ := meadow_resolvent_pair hR
  have hsum : (-C / 3) ^ 3 + (-D / 3) ^ 3 = -complexMonicDepressedQ a b c := by
    dsimp only [D₁] at hs
    unfold complexMonicDepressedQ
    linear_combination -(1 / 27 : ℂ) * hs
  have hprod : (-C / 3) * (-D / 3) = -complexMonicDepressedP a b / 3 := by
    dsimp only [D₀] at hp
    unfold complexMonicDepressedP
    linear_combination (1 / 9 : ℂ) * hp
  let root (ζ : ℂ) := -(a + ζ * C + D₀ / (ζ * C)) / 3
  have hroot (ζ : ℂ) : root ζ = ζ * (-C / 3) + ζ⁻¹ * (-D / 3) - a / 3 := by
    simp only [root, D, div_eq_mul_inv, mul_inv_rev]
    ring
  have hu : omega * omega ^ 2 = 1 := by rw [← pow_succ', omega_cube]
  have hi : omega⁻¹ = omega ^ 2 := inv_eq_of_mul_eq_one_right hu
  have hi₂ : (omega ^ 2)⁻¹ = omega := inv_eq_of_mul_eq_one_left hu
  change (monicCubic a b c).roots = {root 1, root omega, root (omega ^ 2)}
  simp only [hroot, inv_one, one_mul, hi, hi₂]
  exact monicCubic_roots_of_compatible_pair hsum hprod

/-- Apply the monic formula to any cubic with nonzero leading coefficient. -/
theorem cardano_formula_meadowInvariants {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let r := meadowCubicRootsViaInvariants (b / a) (c / a) (d / a)
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = r.x₀ ∨ x = r.x₁ ∨ x = r.x₂ := by
  have h := mem_roots_monicCubic (b / a) (c / a) (d / a) x
  rw [monicCubic_roots_meadowInvariants] at h
  have hscale : a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
      a * x ^ 3 + b * x ^ 2 + c * x + d := by field_simp
  rw [← hscale, mul_eq_zero, or_iff_right ha]
  simpa using h.symm

end CubicEquation.CardanoComplex
