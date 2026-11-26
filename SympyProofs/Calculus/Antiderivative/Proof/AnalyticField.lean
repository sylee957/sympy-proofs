module

public import SympyProofs.Calculus.Antiderivative.Spec.Specialization
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Along a solution of the generator equations, the formal derivative of a regular
rational function specializes to its complex derivative. A continuous logarithm of a
differentiable function has its logarithmic derivative (`hasDerivAt_of_exp_eq`). -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Filter

/-- **Any continuous logarithm has the logarithmic derivative.** If `exp (ℓ w) = u w` near
`z`, with `ℓ` continuous at `z` and `u` differentiable there, then `ℓ` has the derivative
`u′ / u` at `z`. No branch is chosen: near `z` the function `ℓ` differs from a principal
logarithm of `u w / u z` by a constant. -/
theorem hasDerivAt_of_exp_eq {ℓ u : ℂ → ℂ} {u' z : ℂ} (hu : HasDerivAt u u' z)
    (hc : ContinuousAt ℓ z) (he : ∀ᶠ w in nhds z, Complex.exp (ℓ w) = u w) :
    HasDerivAt ℓ (u' / u z) z := by
  have ez : Complex.exp (ℓ z) = u z := he.self_of_nhds
  have uz : u z ≠ 0 := ez ▸ Complex.exp_ne_zero _
  have near := hc.eventually_mem (Metric.ball_mem_nhds (ℓ z) Real.pi_pos)
  have key : ∀ᶠ w in nhds z, ℓ w = ℓ z + Complex.log (u w / u z) := by
    filter_upwards [he, near] with w hw hn
    have him : |(ℓ w - ℓ z).im| < Real.pi :=
      (Complex.abs_im_le_norm _).trans_lt (by rwa [← dist_eq_norm])
    rw [← hw, ← ez, ← Complex.exp_sub,
      Complex.log_exp (by linarith [(abs_lt.mp him).1]) (abs_lt.mp him).2.le]
    ring
  have d : HasDerivAt (fun w => ℓ z + Complex.log (u w / u z)) (u' / u z) z := by
    refine (((hu.div_const (u z)).clog (by
      rw [div_self uz]
      exact Complex.one_mem_slitPlane)).const_add (ℓ z)).congr_deriv ?_
    rw [div_self uz, div_one]
  exact d.congr_of_eventuallyEq key

variable {n : ℕ} {g : ℂ → Fin n → ℂ} {z : ℂ} {v : List (M ℂ n)}

/-- A realization satisfies the generator equations at a point, with regular velocities. -/
def Model.SolvedBy (v : List (M ℂ n)) (g : ℂ → Fin n → ℂ) (z : ℂ) : Prop :=
  ∀ i : Fin n, RegularAt (g z) (v.getD i 0) ∧
    HasDerivAt (fun w => g w i) (evalAt (g z) (v.getD i 0)) z

namespace Model

noncomputable local instance : Algebra ℤ (M ℂ n) := Ring.toIntAlgebra _

private theorem polynomial_chainRule (hg : SolvedBy v g z) (a : MvPolynomial (Fin n) ℂ) :
    ∃ d, HasValue (g z) (derivation ℂ v (polynomial ℂ a)) d ∧
      HasDerivAt (fun w => MvPolynomial.eval (g w) a) d z := by
  induction a using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, by rw [derivation_C]; exact HasValue.zero, ?_⟩
    simpa using hasDerivAt_const z a
  | add a b ha hb =>
    obtain ⟨da, ha, ha'⟩ := ha
    obtain ⟨db, hb, hb'⟩ := hb
    refine ⟨da+db, ?_, ?_⟩
    · simpa only [polynomial, map_add] using ha.add hb
    · simpa only [map_add] using ha'.fun_add hb'
  | mul_X a j ha =>
    obtain ⟨da, ha, ha'⟩ := ha
    obtain ⟨hj, hj'⟩ := hg j
    let q := evalAt (g z) (v.getD j 0)
    refine ⟨da * g z j + MvPolynomial.eval (g z) a * q, ?_, ?_⟩
    · simp only [polynomial, map_mul, Derivation.leibniz, smul_eq_mul]
      change HasValue _ (polynomial ℂ a * derivation ℂ v (polynomial ℂ (MvPolynomial.X j)) +
        polynomial ℂ (MvPolynomial.X j) * derivation ℂ v (polynomial ℂ a)) _
      rw [derivation_X]
      have hX := HasValue.polynomial (p := g z) (MvPolynomial.X j)
      rw [MvPolynomial.eval_X] at hX
      simpa only [add_comm, mul_comm] using
        ((HasValue.polynomial a).mul hj.hasValue).add (hX.mul ha)
    · simpa only [map_mul, MvPolynomial.eval_X] using ha'.fun_mul hj'

/-- Evaluation in a single regular chart commutes with differentiation along a tower solution.
The derivative itself admits a regular chart at the same point. -/
theorem hasDerivAt_evalAt (hg : SolvedBy v g z) {x : M ℂ n} (hx : RegularAt (g z) x) :
    RegularAt (g z) (derivation ℂ v x) ∧
      HasDerivAt (fun w => evalAt (g w) x) (evalAt (g z) (derivation ℂ v x)) z := by
  obtain ⟨c,a,b,hx,hb,_⟩ := hx
  obtain ⟨da,ha,ha'⟩ := polynomial_chainRule hg a
  obtain ⟨db,hb',hb''⟩ := polynomial_chainRule hg b
  let A := polynomial ℂ a
  let B := polynomial ℂ b
  let a₀ := MvPolynomial.eval (g z) a
  let b₀ := MvPolynomial.eval (g z) b
  have hB : B ≠ 0 := by
    intro h
    have he : b = 0 := IsFractionRing.injective _ (M ℂ n) (h.trans (map_zero _).symm)
    simp [he] at hb
  have he : x = A / B := (eq_div_iff hB).mpr hx.symm
  have hD : HasValue (g z) (derivation ℂ v x) ((da*b₀ - a₀*db) / b₀^2) := by
    rw [he, Derivation.leibniz_div]
    simp only [smul_eq_mul, inv_pow, ← div_eq_inv_mul]
    rw [mul_comm B (derivation ℂ v A)]
    have hA := HasValue.polynomial (p := g z) a
    have hv := HasValue.polynomial (p := g z) b
    simpa only [pow_two] using
      (((ha.mul hv).sub (hA.mul hb')).div (hv.mul hv) (mul_ne_zero hb hb))
  refine ⟨⟨_,hD⟩, ?_⟩
  rw [hD.evalAt]
  apply (ha'.fun_div hb'' hb).congr_of_eventuallyEq
  filter_upwards [hb''.continuousAt.eventually_ne hb] with w hw
  apply HasValue.evalAt
  refine ⟨a, b, hx, hw, ?_⟩
  exact (div_mul_cancel₀ _ hw).symm

end Model

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ]

/-- The complex coordinate functions have the prescribed tower velocities at the point. -/
def Tower.SolvedBy (t : Tower R n) (g : ℂ → Fin n → ℂ) (z : ℂ) : Prop :=
  Model.SolvedBy (t.gens.map (val ℂ)) g z

end SympyProofs.Calculus.Antiderivative
