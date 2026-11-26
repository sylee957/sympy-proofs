module

public import SympyProofs.Calculus.Antiderivative.Proof.Tower
public import SympyProofs.Calculus.Antiderivative.Spec.Admissible
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A resonant exponential produces a new constant, and constant-linear rows lose integer
information in exponential degree bounds. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- If a positive multiple of the exponent derivative equals a logarithmic derivative below,
the quotient of the matching generator power and its lower-field factor is constant. -/
theorem D_exp_power_div (t : Tower R n) (u a : K R n) (m : ℕ) (ha : a ≠ 0)
    (h : t.D a / a = (m : K R n) * t.D u) :
    (t.step (.exp u)).D (K.gen ^ m / K.lift a) = 0 := by
  let s := t.step (.exp u)
  change K.derivation s.gens _ = _
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  change _ • (_ • (m • K.gen ^ (m - 1) • s.D K.gen) - K.gen ^ m • s.D (K.lift a)) = _
  rw [D_gen_exp, D_lift, (div_eq_iff ha).mp h]
  cases m with
  | zero => simp
  | succ j => simp only [Nat.add_one_sub_one, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast,
      pow_succ]; ring

/-- A positive power of the new generator divided by a nonzero lower-field element lies
outside the lower field. -/
theorem exp_power_div_ne_lift {a : K R n} (ha : a ≠ 0) {m : ℕ} (hm : 0 < m) (b : K R n) :
    K.gen ^ m / K.lift a ≠ K.lift b := by
  intro h
  have he := congrArg (fun z : K R (n + 1) => Model.stepEquiv R n (K.equiv z))
    ((div_eq_iff ((map_ne_zero K.lift).mpr ha)).mp h)
  simp only [map_pow, map_mul, K.stepEquiv_gen, K.stepEquiv_lift] at he
  rw [← map_mul RatFunc.C] at he
  have hp : (Polynomial.X : Polynomial (M R n)) ^ m = Polynomial.C (K.equiv b * K.equiv a) :=
    RatFunc.algebraMap_injective (M R n) (by simpa using he)
  have hd := congrArg Polynomial.natDegree hp
  simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hd
  omega

/-- A lower-field logarithmic derivative shifted by `m` exponential velocities gives an
equation with a solution of degree `m` in the new generator. -/
theorem exp_power_solution (t : Tower R n) (u a : K R n) (ha : a ≠ 0) (m : ℕ) :
    let y := K.gen ^ m / K.lift a
    (t.step (.exp u)).D y + K.lift (t.D a / a - (m : K R n) * t.D u) * y = 0 := by
  let s := t.step (.exp u)
  change K.derivation s.gens (_ / _) + _ = _
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  change _ • (_ • (m • K.gen ^ (m - 1) • s.D K.gen) - K.gen ^ m • s.D (K.lift a)) + _ = _
  rw [D_gen_exp, D_lift]
  have h := (map_ne_zero K.lift).mpr ha
  cases m <;> simp [smul_eq_mul, nsmul_eq_mul, map_div₀, pow_succ] <;> field_simp <;> ring

end Tower

namespace Exponential

/-- A pair of constant-linear constraints that allow the two independent coefficient vectors
`(0, α⁻¹)` and `(1, m)` must vanish. This applies row by row when both linear combinations
are logarithmic derivatives, regardless of the size of the exponent `m`. -/
theorem row_eq_zero {F : Type*} [Field F] {a b α : F} (hα : α ≠ 0) (m : ℕ)
    (h₀ : a * 0 + b * α⁻¹ = 0) (h₁ : a * 1 + b * (m : F) = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by simpa [hα] using h₀
  exact ⟨by simpa [hb] using h₁, hb⟩

/-- If `v = α · ℓ` and `ℓ` is a logarithmic derivative, a sound constant-linear row for
`[(1 - m α) · ℓ, v]` is zero on both columns. Thus its entries cannot bound `m`. -/
theorem trivial_rows_for_exponent {k F : Type*} [Field k] [Field F] (ι : k →+* F)
    (isLog : F → Prop) {ℓ : F} (hℓ : isLog ℓ) {α : k} (hα : α ≠ 0) (m : ℕ)
    {a b : k} (row : ∀ c d : k,
      isLog (ι c * ((1 - (m : F) * ι α) * ℓ) + ι d * (ι α * ℓ)) → a * c + b * d = 0) :
    a = 0 ∧ b = 0 := by
  apply row_eq_zero hα m
  · apply row
    simpa [map_inv₀, ← mul_assoc, (map_ne_zero ι).mpr hα] using hℓ
  · apply row
    convert hℓ using 1
    simp only [map_one, one_mul, map_natCast]
    ring

end Exponential

end SympyProofs.Calculus.Antiderivative
