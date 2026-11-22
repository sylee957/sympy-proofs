module

public import SympyProofs.RealCubeRoot.Principal
public import SympyProofs.CubicEquation.CardanoComplex.Basic

/-!
# Cardano's formula with the principal complex cube root

For `x^3 + p*x + q = 0`, put `A = -q/2 + sqrt(D)` and
`B = -q/2 - sqrt(D)`, where `D = q^2/4 + p^3/27`.
We take `u = principal A`. The second cube root must be paired: take
`v = -p/(3*u)` when `u != 0`, and `v = principal B` otherwise.
The direct formula using cubic surds is proved separately in `CardanoReal/CubicSurd/Formula.lean`.

The three Cardano expressions factor the polynomial exactly. Consequently the
root lists below are sound and complete, including repeated and triple roots.
The theorem for general coefficients requires a nonzero leading coefficient.
See `cardano_formula_principal` for the equation and all intermediate quantities together
in a single theorem statement using `let` bindings.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open Complex
open scoped ComplexConjugate

/-- The first cube root uses the principal complex branch. -/
def u (p q : ℂ) : ℂ := principal (radicandPlus p q)

/-- The second root is paired to ensure `u*v = -p/3`; the zero case is explicit. -/
def v (p q : ℂ) : ℂ :=
  if u p q = 0 then principal (radicandMinus p q) else -p / (3 * u p q)

@[simp] theorem u_cube (p q : ℂ) : u p q ^ 3 = radicandPlus p q := principal_cube _

theorem p_eq_zero_of_u_eq_zero {p q : ℂ} (hu : u p q = 0) : p = 0 := by
  have hA : radicandPlus p q = 0 := by simpa [hu] using (u_cube p q).symm
  have hp : (-p / 3) ^ 3 = 0 := by
    rw [← radicands_product, hA, zero_mul]
  have h := eq_zero_of_pow_eq_zero hp
  simpa using h

theorem uv (p q : ℂ) : u p q * v p q = -p / 3 := by
  unfold v
  split_ifs with hu
  · rw [hu, zero_mul, p_eq_zero_of_u_eq_zero hu]
    norm_num
  · field_simp

@[simp] theorem v_cube (p q : ℂ) : v p q ^ 3 = radicandMinus p q := by
  by_cases hu : u p q = 0
  · simp [v, hu]
  · apply mul_left_cancel₀ (pow_ne_zero 3 hu)
    calc
      u p q ^ 3 * v p q ^ 3 = (u p q * v p q) ^ 3 := (mul_pow _ _ _).symm
      _ = (-p / 3) ^ 3 := by rw [uv]
      _ = u p q ^ 3 * radicandMinus p q := by rw [u_cube, radicands_product]

def depressedRoots (p q : ℂ) : List ℂ := pairedRoots (u p q) (v p q)

/-- Soundness and completeness: these are exactly all roots of the depressed cubic. -/
theorem mem_depressedRoots_iff (p q x : ℂ) :
    x ∈ depressedRoots p q ↔ x ^ 3 + p * x + q = 0 := by
  apply mem_pairedRoots_iff
  · rw [u_cube, v_cube, radicands_sum]
  · exact uv p q

theorem depressed_factorization (p q x : ℂ) :
    (x - (u p q + v p q)) *
      (x - (omega * u p q + omega ^ 2 * v p q)) *
      (x - (omega ^ 2 * u p q + omega * v p q)) = x ^ 3 + p * x + q := by
  rw [factorization_identity, uv, u_cube, v_cube, radicands_sum]
  ring

/-- One explicit solution, valid also when a radical is zero. -/
theorem depressed_root_spec (p q : ℂ) :
    (u p q + v p q) ^ 3 + p * (u p q + v p q) + q = 0 :=
  (mem_depressedRoots_iff p q _).mp (by simp [depressedRoots, pairedRoots])

def cubicRoots (a b c d : ℂ) : List ℂ :=
  (depressedRoots (depressedP a b c) (depressedQ a b c d)).map
    (fun z => z - (b / a) / 3)

/-- Every cubic with nonzero leading coefficient is solved by the three Cardano
expressions, and every solution occurs in the list. Coefficients may be complex. -/
theorem mem_cubicRoots_iff {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    x ∈ cubicRoots a b c d ↔ a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  have hmem : x ∈ cubicRoots a b c d ↔
      x + (b / a) / 3 ∈ depressedRoots (depressedP a b c) (depressedQ a b c d) := by
    simp only [cubicRoots, List.mem_map]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : x + (b / a) / 3 = y := by linear_combination -heq
      rwa [hxy]
    · intro hx
      exact ⟨x + (b / a) / 3, hx, by ring⟩
  rw [hmem, mem_depressedRoots_iff, depressed_shift]
  have hscale : a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
      a * x ^ 3 + b * x ^ 2 + c * x + d := by
    field_simp
  rw [← hscale, mul_eq_zero]
  simp [ha]

/-- Cardano's formula in one place: the equation, intermediate quantities, and
all three solutions. For complex coefficients, `v` is paired with `u` so that
`u * v = -p / 3`. The explicit zero case also covers degenerate radicals. -/
theorem cardano_formula_principal {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let s := Complex.sqrt Δ
    let u := principal (-q / 2 + s)
    let v := if u = 0 then principal (-q / 2 - s) else -p / (3 * u)
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  change a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
    x = u (depressedP a b c) (depressedQ a b c d) +
      v (depressedP a b c) (depressedQ a b c d) - (b / a) / 3 ∨
    x = omega * u (depressedP a b c) (depressedQ a b c d) +
      omega ^ 2 * v (depressedP a b c) (depressedQ a b c d) - (b / a) / 3 ∨
    x = omega ^ 2 * u (depressedP a b c) (depressedQ a b c d) +
      omega * v (depressedP a b c) (depressedQ a b c d) - (b / a) / 3
  simpa only [cubicRoots, depressedRoots, pairedRoots, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using
    (mem_cubicRoots_iff ha b c d x).symm

/-- A single-valued Cardano solution to a general cubic. -/
def cubicRoot (a b c d : ℂ) : ℂ :=
  u (depressedP a b c) (depressedQ a b c d) +
    v (depressedP a b c) (depressedQ a b c d) - (b / a) / 3

theorem cubicRoot_spec {a : ℂ} (ha : a ≠ 0) (b c d : ℂ) :
    a * cubicRoot a b c d ^ 3 + b * cubicRoot a b c d ^ 2 +
      c * cubicRoot a b c d + d = 0 := by
  apply (mem_cubicRoots_iff ha b c d _).mp
  apply List.mem_map.mpr
  exact ⟨_, by simp [depressedRoots, pairedRoots], rfl⟩

end CubicEquation.CardanoComplex
