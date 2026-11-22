module

public import SympyProofs.CubicEquation.CardanoComplex.Principal.Formula

/-!
# Cardano's formula for real coefficients: shared lemmas

For real `p,q`, conjugation either fixes the two Cardano radicands or exchanges
them. Hence any function `S` commuting with conjugation sends them to a pair
with real sum and real product, and if `S` is also a total cube root, the
product is `-p/3`. No quotient correction is needed.

`symmetric_cubic_roots_iff_of_cube_conj` concludes that the three Cardano
values built from such an `S` are exactly the solutions of a real cubic with
nonzero leading coefficient. Every formula in `CardanoReal` is an instance.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

def realDiscriminant (p q : ℝ) : ℝ := q ^ 2 / 4 + p ^ 3 / 27

theorem discriminant_ofReal (p q : ℝ) :
    discriminant (p : ℂ) q = (realDiscriminant p q : ℂ) := by
  simp [discriminant, realDiscriminant, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow]

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

end CubicEquation.CardanoReal
