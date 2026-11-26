module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Tan
public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants
public import SympyProofs.Calculus.Antiderivative.Proof.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The exponential change of variable for a tangent, its inverse, and its derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Tan

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

private theorem gen_denom : (K.gen : K R (n + 1)) + 1 ≠ 0 := by
  intro h
  have he := Tower.exp_power_div_ne_lift (R := R) (n := n) (a := 1) one_ne_zero
    (m := 1) (by decide) (-1)
  simp only [pow_one, map_one, div_one, map_neg] at he
  exact he (eq_neg_of_add_eq_zero_left h)

private theorem constantD (t : Tower R n) (i : K R 0) : t.D (K.ofConst i) = 0 := by
  apply (val (FractionRing R)).injective
  rw [map_zero, Tower.val_D, ← Model.C_constantHom, Tower.modelD_C]

/-- The tangent generator has derivative u′(1+tan² u). -/
theorem generator_deriv (t : Tower R n) (i : K R 0) (hi : i ^ 2 = -1) (u : K R n) :
    (tower t i u).D (generator i) = K.lift (t.D u) * (1 + generator i ^ 2) := by
  let s := tower t i u
  let d := K.derivation s.gens
  let j := (K.ofConst i : K R (n + 1))
  let z := (K.gen : K R (n + 1))
  have hj : j ^ 2 = -1 := by simpa [j] using congrArg (K.ofConst (n := n + 1)) hi
  have hdj : d j = 0 := constantD s i
  have hlow : t.D (2 * K.ofConst i * u) = 2 * K.ofConst i * t.D u := by
    change K.derivation t.gens _ = _
    have hc : K.derivation t.gens (K.ofConst i) = 0 := constantD t i
    have htwo : K.derivation t.gens 2 = 0 := (K.derivation t.gens).map_natCast 2
    simp [Derivation.leibniz, hc, htwo, Tower.D]
  have hz : d z = 2 * j * K.lift (t.D u) * z := by
    change (t.step (.exp _)).D K.gen = _
    rw [Tower.D_gen_exp, hlow]
    have hjl : K.lift (K.ofConst i : K R n) = j := by
      apply (val (FractionRing R)).injective
      simp only [j, val_lift, ← Model.C_constantHom, Model.includeVars_C]
    simp only [map_mul, hjl, show K.lift (2 : K R n) = 2 from map_ofNat _ _, z]
  have hden : z + 1 ≠ 0 := gen_denom
  change d (-j * (z - 1) / (z + 1)) = _ * (1 + (-j * (z - 1) / (z + 1)) ^ 2)
  rw [Derivation.leibniz_div, Derivation.leibniz, map_neg, map_sub, map_add, hdj, hz,
    Derivation.map_one_eq_zero]
  simp only [smul_eq_mul, neg_zero, mul_zero, add_zero, sub_zero]
  field_simp [hden]
  linear_combination -(K.lift (t.D u)) * (z + 1) ^ 2 * hj

/-- The tangent generates the full exponential field when the constants contain i. -/
theorem exponential_generator [CharZero R] (i : K R 0) (hi : i ^ 2 = -1) :
    exponential i (generator i : K R (n + 1)) = K.gen := by
  let j := (K.ofConst i : K R (n + 1))
  let z := (K.gen : K R (n + 1))
  have hj : j ≠ 0 := by
    have hj2 : j ^ 2 = -1 := by simpa [j] using congrArg (K.ofConst (n := n + 1)) hi
    intro h
    simp [h] at hj2
  have hd : z + 1 ≠ 0 := gen_denom
  change (j - -j * (z - 1) / (z + 1)) / (j + -j * (z - 1) / (z + 1)) = z
  have h : j + -j * (z - 1) / (z + 1) = (2 * j) / (z + 1) := by field_simp; ring
  rw [h]
  field_simp
  ring

end SympyProofs.Calculus.Antiderivative.Kind.Tan
