module

public import SympyProofs.CubicEquation.CardanoComplex.CompatiblePair

/-!
# Cardano's formula with principal radicals and meadow inverse

For the depressed cubic let A = -q/2 + √(q²/4 + p³/27). The two Cardano
radicands sum to -q. Thus A - (1 - A*A⁻¹)*q selects A when it is nonzero
and the other radicand when A is zero. Taking its principal cube root U
leaves V = (-p/3)*U⁻¹. Both inverses use the field convention 0⁻¹ = 0.
The expression uses one coefficient-dependent square root and one cube root.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot

/-- Select the radicand arithmetically before taking its principal cube root. -/
def meadowU (p q : ℂ) : ℂ :=
  let A := radicandPlus p q
  principal (A - (1 - A * A⁻¹) * q)

/-- For two radicands with sum s and product t³, select the first nonzero
radicand before taking the cube root. The all-zero case gives C = D = 0. -/
theorem meadow_resolvent_pair {A s t : ℂ} (h : A * (s - A) = t ^ 3) :
    let C := principal (A + (1 - A * A⁻¹) * s)
    let D := t * C⁻¹
    C ^ 3 + D ^ 3 = s ∧ C * D = t := by
  by_cases hA : A = 0
  · subst A
    have ht : t = 0 := eq_zero_of_pow_eq_zero (n := 3) (by simpa using h.symm)
    simp [ht]
  · have hc : principal A ≠ 0 := fun hz => hA (by simpa [hz] using (principal_cube A).symm)
    simp only [mul_inv_cancel₀ hA, sub_self, zero_mul, add_zero]
    constructor
    · rw [mul_pow, inv_pow, principal_cube, ← h]
      field_simp [hA]
      ring
    · field_simp

/-- The meadow formulas give a compatible pair, including at the triple root. -/
theorem meadow_pair (p q : ℂ) :
    let U := meadowU p q
    let V := (-p / 3) * U⁻¹
    U ^ 3 + V ^ 3 = -q ∧ U * V = -p / 3 := by
  have h : radicandPlus p q * (-q - radicandPlus p q) = (-p / 3) ^ 3 := by
    rw [← radicands_sum p q, add_sub_cancel_left, radicands_product]
  simpa only [meadowU, mul_neg, ← sub_eq_add_neg] using meadow_resolvent_pair h

/-- The three roots, shifted back to the original variable. -/
def meadowCubicRoots (a b c d : ℂ) : CardanoRoots :=
  let p := c / a - (b / a) ^ 2 / 3
  let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let A := -q / 2 + Complex.sqrt (q ^ 2 / 4 + p ^ 3 / 27)
  let U := (A - (1 - A * A⁻¹) * q) ^ (3⁻¹ : ℂ)
  let V := (-p / 3) * U⁻¹
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2
  let shift := (b / a) / 3
  ⟨U + V - shift, ω * U + ω ^ 2 * V - shift, ω ^ 2 * U + ω * V - shift⟩

/-- For every genuine cubic, the three meadow expressions give exactly its solutions. -/
theorem cardano_formula_meadow {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let r := meadowCubicRoots a b c d
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = r.x₀ ∨ x = r.x₁ ∨ x = r.x₂ := by
  obtain ⟨hs, hp⟩ := meadow_pair (depressedP a b c) (depressedQ a b c d)
  exact cubic_formula_of_compatible_pair ha b c d x _ _ hs hp

/-- The formula also gives the multiplicity of each root of the monic cubic. -/
theorem monicCubic_roots_meadow (a b c : ℂ) :
    let r := meadowCubicRoots 1 a b c
    (monicCubic a b c).roots = {r.x₀, r.x₁, r.x₂} := by
  obtain ⟨hs, hp⟩ := meadow_pair (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
  simpa only [meadowCubicRoots, meadowU, radicandPlus, discriminant, principal, omega, div_one,
    complexMonicDepressedP, complexMonicDepressedQ] using
    monicCubic_roots_of_compatible_pair hs hp

end CubicEquation.CardanoComplex
