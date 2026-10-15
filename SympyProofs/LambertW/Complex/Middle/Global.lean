import SympyProofs.LambertW.Complex.Middle.GlobalInverse
import SympyProofs.LambertW.Complex.Middle.Uniqueness

/-! # The analytic real-lower extension on the double-cut domain

This branch agrees with `Real.lower` on `(-1/e, 0)`. It is distinct from the
indexed branch `(branch (-1))`, which uses a different cut. Outside `middleDomain`,
the total function is unspecified.
-/
namespace LambertW.Complex
open Set Filter Topology

/-- The complement of the real rays `(-∞, -1/e]` and `[0, ∞)`. -/
def middleDomain : Set ℂ :=
  {z | z.im ≠ 0 ∨ (-Real.exp (-1) < z.re ∧ z.re < 0)}

@[simp] theorem ofReal_mem_middleDomain {x : ℝ} :
    (x : ℂ) ∈ middleDomain ↔ x ∈ Ioo (-Real.exp (-1)) 0 := by
  simp [middleDomain]

theorem isOpen_middleDomain : IsOpen middleDomain :=
  (isOpen_ne.preimage Complex.continuous_im).union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))

theorem starConvex_middleDomain {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    StarConvex ℝ (x : ℂ) middleDomain := by
  intro y hy a b ha hb hab
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using ofReal_mem_middleDomain.mpr hx
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  change _ ≠ 0 ∨ (_ < _ ∧ _ < _)
  simp only [Complex.add_im, Complex.add_re, Complex.smul_im, Complex.smul_re,
    Complex.ofReal_im, Complex.ofReal_re, smul_eq_mul, mul_zero, zero_add]
  rcases hy with hy | hy
  · exact Or.inl (mul_ne_zero hb0 hy)
  · right
    constructor
    · nlinarith [mul_nonneg ha (le_of_lt (sub_pos.mpr hx.1)), mul_pos hbpos (sub_pos.mpr hy.1)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hx.2),
        mul_neg_of_pos_of_neg hbpos hy.2]

noncomputable def middleBase : ℝ := -Real.exp (-1) / 2

theorem middleBase_mem : middleBase ∈ Ioo (-Real.exp (-1)) 0 := by
  have hp := Real.exp_pos (-1)
  constructor <;> unfold middleBase <;> linarith

theorem middleDomain_ne_zero {z : ℂ} (hz : z ∈ middleDomain) : z ≠ 0 := by
  rintro rfl
  simp [middleDomain] at hz

theorem middleDomain_ne_criticalValue {z : ℂ} (hz : z ∈ middleDomain) :
    z ≠ -Complex.exp (-1) := by
  rintro rfl
  have he : -Complex.exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) := by simp
  rw [he, ofReal_mem_middleDomain] at hz
  exact lt_irrefl _ hz.1

theorem exists_middle :
    ∃ W : ℂ → ℂ, AnalyticOnNhd ℂ W middleDomain ∧
      W middleBase = (Real.lower middleBase : ℂ) ∧
      ∀ z ∈ middleDomain, mulExp (W z) = z := by
  apply exists_analytic_inverse_on_starDomain isOpen_middleDomain
    (starConvex_middleDomain middleBase_mem) (ofReal_mem_middleDomain.mpr middleBase_mem)
    (fun _ hz => middleDomain_ne_zero hz) (fun _ hz => middleDomain_ne_criticalValue hz)
  rw [mulExp_ofReal, Real.mulExp_lower ⟨le_of_lt middleBase_mem.1, middleBase_mem.2⟩]

/-- The analytic real-lower extension; specified only on `middleDomain`. -/
noncomputable def middle : ℂ → ℂ := exists_middle.choose

theorem analyticOnNhd_middle : AnalyticOnNhd ℂ middle middleDomain :=
  exists_middle.choose_spec.1

@[simp] theorem middle_base : middle middleBase = (Real.lower middleBase : ℂ) :=
  exists_middle.choose_spec.2.1

theorem mulExp_middle {z : ℂ} (hz : z ∈ middleDomain) : mulExp (middle z) = z :=
  exists_middle.choose_spec.2.2 z hz

/-- Agreement throughout the entire real interval. -/
theorem middle_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    middle (x : ℂ) = (Real.lower x : ℂ) := by
  let S := Ioo (-Real.exp (-1)) (0 : ℝ)
  let : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Ioo
  have hF : Continuous (fun t : S => middle (t : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((analyticOnNhd_middle _ (ofReal_mem_middleDomain.mpr t.property)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).comp continuous_subtype_val.continuousAt
  have hG : Continuous (fun t : S => (Real.lower t : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_lower t.property).comp continuous_subtype_val.continuousAt)
  have hi (t : S) : mulExp (middle (t : ℂ)) = mulExp (Real.lower t : ℂ) := by
    rw [mulExp_middle (ofReal_mem_middleDomain.mpr t.property), mulExp_ofReal,
      Real.mulExp_lower ⟨le_of_lt t.property.1, t.property.2⟩]
  have hn (t : S) : mulExp (middle (t : ℂ)) ≠ -Complex.exp (-1) := by
    rw [mulExp_middle (ofReal_mem_middleDomain.mpr t.property)]
    exact middleDomain_ne_criticalValue (ofReal_mem_middleDomain.mpr t.property)
  have he := eq_of_continuous_mulExp_lifts hF hG hi hn
    (t₀ := (⟨middleBase, middleBase_mem⟩ : S)) middle_base
  exact congrFun he (⟨x, hx⟩ : S)

theorem middle_mul_exp {z : ℂ} (hz : z ∈ middleDomain) :
    middle z * Complex.exp (middle z) = z := mulExp_middle hz

theorem deriv_middle {z : ℂ} (hz : z ∈ middleDomain) :
    deriv middle z = (Complex.exp (middle z) * (1 + middle z))⁻¹ := by
  apply deriv_of_eventually_mulExp_eq (analyticOnNhd_middle z hz).differentiableAt
  filter_upwards [isOpen_middleDomain.mem_nhds hz] with y hy
  exact mulExp_middle hy

theorem hasDerivAt_middle {z : ℂ} (hz : z ∈ middleDomain) :
    HasDerivAt middle (Complex.exp (middle z) * (1 + middle z))⁻¹ z := by
  rw [← deriv_middle hz]
  exact (analyticOnNhd_middle z hz).differentiableAt.hasDerivAt

theorem continuousOn_middle : ContinuousOn middle middleDomain :=
  fun z hz => (analyticOnNhd_middle z hz).continuousAt.continuousWithinAt

theorem injOn_middle : InjOn middle middleDomain := by
  intro x hx y hy he
  have hh := congrArg mulExp he
  simpa only [mulExp_middle hx, mulExp_middle hy] using hh

/-- One real normalization uniquely selects the global analytic middle inverse. -/
theorem eqOn_middle {W : ℂ → ℂ} (hW : AnalyticOnNhd ℂ W middleDomain)
    (hbase : W middleBase = (Real.lower middleBase : ℂ))
    (hinv : ∀ z ∈ middleDomain, mulExp (W z) = z) : EqOn W middle middleDomain := by
  exact eqOn_middle_of_isPreconnected isOpen_middleDomain
    ((starConvex_middleDomain middleBase_mem).isPathConnected
      (ofReal_mem_middleDomain.mpr middleBase_mem)).isConnected.isPreconnected
    middleBase_mem (ofReal_mem_middleDomain.mpr middleBase_mem)
    hW analyticOnNhd_middle hbase middle_base hinv (fun _ hz => mulExp_middle hz)

/-- Compatibility with every previously constructed real-centered local inverse. -/
theorem eventuallyEq_middle_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    middle =ᶠ[𝓝 (x : ℂ)] localMiddle x hx := by
  apply eventuallyEq_localMiddle hx
    (analyticOnNhd_middle _ (ofReal_mem_middleDomain.mpr hx)).continuousAt (middle_ofReal hx)
  filter_upwards [isOpen_middleDomain.mem_nhds (ofReal_mem_middleDomain.mpr hx)] with z hz
  exact mulExp_middle hz

/-- The real restriction has zero imaginary part throughout the interval. -/
@[simp] theorem im_middle_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    (middle (x : ℂ)).im = 0 := by
  rw [middle_ofReal hx, Complex.ofReal_im]

/-- The other inverse identity on the image of the double-cut domain. -/
theorem middle_mulExp {w : ℂ} (hw : w ∈ middle '' middleDomain) :
    middle (mulExp w) = w := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [mulExp_middle hz]

/-- Any analytic right inverse agreeing with the real lower branch agrees
with `middle` everywhere in the double-cut domain. -/
theorem eqOn_middle_of_real_agreement {W : ℂ → ℂ}
    (hW : AnalyticOnNhd ℂ W middleDomain)
    (hinv : ∀ z ∈ middleDomain, mulExp (W z) = z)
    (hreal : ∀ x ∈ Ioo (-Real.exp (-1)) 0, W (x : ℂ) = (Real.lower x : ℂ)) :
    EqOn W middle middleDomain :=
  eqOn_middle hW (hreal middleBase middleBase_mem) hinv

/-- The capstone: a global analytic inverse extending the entire real lower branch.
Uniqueness is on the domain, since values outside it are unspecified. -/
theorem exists_middle_analytic_extension :
    ∃ W : ℂ → ℂ, AnalyticOnNhd ℂ W middleDomain ∧
      (∀ z ∈ middleDomain, mulExp (W z) = z) ∧
      (∀ x ∈ Ioo (-Real.exp (-1)) 0, W (x : ℂ) = (Real.lower x : ℂ)) ∧
      ∀ V : ℂ → ℂ, AnalyticOnNhd ℂ V middleDomain →
        (∀ z ∈ middleDomain, mulExp (V z) = z) →
        (∀ x ∈ Ioo (-Real.exp (-1)) 0, V (x : ℂ) = (Real.lower x : ℂ)) →
        EqOn V W middleDomain := by
  exact ⟨middle, analyticOnNhd_middle, fun _ hz => mulExp_middle hz,
    fun _ hx => middle_ofReal hx, fun _ hV hi hr => eqOn_middle_of_real_agreement hV hi hr⟩

end LambertW.Complex
