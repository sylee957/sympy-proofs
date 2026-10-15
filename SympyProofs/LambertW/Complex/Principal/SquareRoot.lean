import SympyProofs.LambertW.Complex.Boundary.Internal.Principal.BranchPoint
import Mathlib.Analysis.Analytic.Order

/-!
# Leading square-root behavior at the branch point

Writing `b = -exp (-1)`, the squared displacement satisfies
`(W(z) + 1)^2 / (z - b) → 2 * exp 1` for either boundary convention.
This also gives the square-root asymptotic for its magnitude in every direction.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- The forward map has a double zero after translating its critical point.
The nonvanishing analytic factor has value `exp (-1) / 2`. -/
theorem exists_mulExp_branchPoint_factor :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = Complex.exp (-1) / 2 ∧
      ∀ u : ℂ, mulExp (u - 1) - mulExp (-1) = u ^ 2 * g u := by
  let f : ℂ → ℂ := fun u => mulExp (u - 1) - mulExp (-1)
  have hsub : AnalyticAt ℂ (fun u : ℂ => u - 1) 0 := by fun_prop
  have ha : AnalyticAt ℂ f 0 :=
    ((analyticAt_mulExp ((0 : ℂ) - 1)).comp (f := fun u : ℂ => u - 1) (x := 0) hsub).sub analyticAt_const
  have hd (u : ℂ) : HasDerivAt f (Complex.exp (u - 1) * u) u := by
    convert ((hasDerivAt_mulExp (u - 1)).comp u
      ((hasDerivAt_id u).sub_const 1)).sub_const (mulExp (-1)) using 1
    · rfl
    · ring
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : iteratedDeriv 1 f 0 = 0 := by simpa [iteratedDeriv_one] using (hd 0).deriv
  have hf2 : iteratedDeriv 2 f 0 = Complex.exp (-1) := by
    have he : deriv f = fun u => Complex.exp (u - 1) * u := funext fun u => (hd u).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, he]
    have h := (((Complex.hasDerivAt_exp ((0 : ℂ) - 1)).comp 0
      ((hasDerivAt_id (0 : ℂ)).sub_const 1)).mul (hasDerivAt_id (0 : ℂ))).deriv
    convert h using 2 <;> norm_num
    congr 1
  obtain ⟨R, hR, h⟩ := ha.exists_eq_sum_add_pow_mul 3
  refine ⟨fun u => Complex.exp (-1) / 2 + u * R u,
    analyticAt_const.add (analyticAt_id.mul hR), by simp, ?_⟩
  intro u
  have hu := h u
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
    hf0, hf1, hf2, smul_eq_mul] at hu
  norm_num at hu
  dsimp [f] at hu
  convert hu using 1; ring

/-- The quadratic relation, independent of the boundary convention. -/
theorem BoundaryInternal.tendsto_principalModel_sq_div (side : BoundarySide) :
    Tendsto (fun z : ℂ => (BoundaryInternal.principalModel side z + 1) ^ 2 /
        (z - ((-Real.exp (-1) : ℝ) : ℂ)))
      (𝓝[≠] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (2 * Complex.exp 1)) := by
  let b : ℂ := ((-Real.exp (-1) : ℝ) : ℂ)
  obtain ⟨g, hg, hg0, he⟩ := exists_mulExp_branchPoint_factor
  have hb : mulExp (-1) = b := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, mulExp_ofReal, Real.mulExp_neg_one]
  have hw : Tendsto (fun z => BoundaryInternal.principalModel side z + 1) (𝓝[≠] b) (𝓝 0) := by
    have h := (BoundaryInternal.continuousAt_principalModel_branchPoint side).tendsto.add_const 1
    simpa only [BoundaryInternal.principalModel_branchPoint, neg_add_cancel] using h.mono_left (nhdsWithin_le_nhds : 𝓝[≠] b ≤ 𝓝 b)
  have ht := (hg.continuousAt.tendsto.comp hw).inv₀ (by rw [hg0]; exact div_ne_zero (Complex.exp_ne_zero _) (by norm_num))
  have hc : (g 0)⁻¹ = 2 * Complex.exp 1 := by
    rw [hg0, inv_div, Complex.exp_neg]
    simp [div_eq_mul_inv]
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ b := hz
  have h : z - b = (BoundaryInternal.principalModel side z + 1) ^ 2 * g (BoundaryInternal.principalModel side z + 1) := by
    simpa only [add_sub_cancel_right, BoundaryInternal.mulExp_principalModel, hb] using
      he (BoundaryInternal.principalModel side z + 1)
  have hu : BoundaryInternal.principalModel side z + 1 ≠ 0 := by
    intro hu
    rw [hu, zero_pow (by decide), zero_mul] at h
    exact hz' (sub_eq_zero.mp h)
  rw [h]
  dsimp only [Function.comp_def]
  field_simp

/-- Square-root growth of the magnitude, valid from every direction and for
both choices of boundary values. -/
theorem BoundaryInternal.tendsto_norm_principalModel_div_sqrt (side : BoundarySide) :
    Tendsto (fun z : ℂ => ‖BoundaryInternal.principalModel side z + 1‖ /
        Real.sqrt ‖z - ((-Real.exp (-1) : ℝ) : ℂ)‖)
      (𝓝[≠] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (Real.sqrt (2 * Real.exp 1))) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (BoundaryInternal.tendsto_principalModel_sq_div side).norm
  simpa only [Function.comp_def, norm_div, norm_pow, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), norm_mul, Complex.norm_exp, Complex.one_re,
    Complex.norm_ofNat] using h

/-- On the real principal branch the positive square root is selected:
`(W(x) + 1) / sqrt (x + 1/e) → sqrt (2e)` as `x → -1/e` from the right. -/
theorem tendsto_real_principal_div_sqrt :
    Tendsto (fun x : ℝ => (Real.principal x + 1) / Real.sqrt (x + Real.exp (-1)))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (Real.sqrt (2 * Real.exp 1))) := by
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (-Real.exp (-1)))
      (𝓝[≠] ((-Real.exp (-1) : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change (x : ℂ) ≠ ((-Real.exp (-1) : ℝ) : ℂ)
      have hx' : -Real.exp (-1) < x := hx
      exact_mod_cast ne_of_gt hx'
  have h := (BoundaryInternal.tendsto_norm_principalModel_div_sqrt .upper).comp hc
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change -Real.exp (-1) < x at hx
  dsimp only [Function.comp_def]
  rw [BoundaryInternal.principalModel_ofReal _ (le_of_lt hx)]
  have hp : 0 ≤ Real.principal x + 1 := by
    have hh := Real.principal_mem (le_of_lt hx)
    change -1 ≤ Real.principal x at hh
    linarith
  have hd : 0 ≤ x + Real.exp (-1) := by linarith
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  simp only [Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add,
    abs_of_nonneg hp, abs_of_nonneg hd]

end LambertW.Complex
