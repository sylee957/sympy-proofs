import SympyProofs.RouthHurwitz.Roots.Reflection

/-! Local root behavior at affine degree-reduction endpoints. -/
namespace Polynomial
attribute [local instance] Classical.propDecidable

/-- A boundary root whose full multiplicity divides the perturbation remains
fixed: no other roots can converge to it. -/
theorem affine_root_eventually_eq (A B : ℂ[X]) (hA : A ≠ 0) (z : ℂ)
    (hB : (X - C z) ^ A.rootMultiplicity z ∣ B)
    (t r : ℕ → ℂ) (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hr : Filter.Tendsto r Filter.atTop (nhds z))
    (hroot : ∀ k, (A + C (t k) * B).IsRoot (r k)) :
    ∀ᶠ k in Filter.atTop, r k = z := by
  let g := A /ₘ (X - C z) ^ A.rootMultiplicity z
  obtain ⟨b, hb⟩ := hB
  have hg : g.eval z ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero z hA
  have hfac : A = (X - C z) ^ A.rootMultiplicity z * g :=
    (pow_mul_divByMonic_rootMultiplicity_eq A z).symm
  have hlim : Filter.Tendsto (fun k => g.eval (r k) + t k * b.eval (r k))
      Filter.atTop (nhds (g.eval z)) := by
    simpa using (g.continuous.tendsto z |>.comp hr).add
      (ht.mul (b.continuous.tendsto z |>.comp hr))
  filter_upwards [hlim.eventually_ne hg] with k hk
  have he := hroot k
  have heq : (A + C (t k) * B).eval (r k) =
      (r k - z) ^ A.rootMultiplicity z * (g.eval (r k) + t k * b.eval (r k)) := by
    conv_lhs => rw [hfac, hb]
    simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    ring
  rw [IsRoot, heq] at he
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he).resolve_right hk))

/-- The root arriving at zero after reciprocal reversal has the sign
opposite the real leading-coefficient ratio. -/
theorem affine_zero_root_sign (g B : ℂ[X]) (hg : g.eval 0 ≠ 0) (c : ℝ)
    (hc : c ≠ 0) (hB : B.eval 0 = (c : ℂ) * g.eval 0)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k)
    (r : ℕ → ℂ) (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hroot : ∀ k, (X * g + C (t k : ℂ) * B).IsRoot (r k)) :
    ∀ᶠ k in Filter.atTop, (0 < (r k).re ↔ c < 0) := by
  have hG := g.continuous.tendsto 0 |>.comp hr
  have hD := B.continuous.tendsto 0 |>.comp hr
  let b (k : ℕ) : ℂ := -B.eval (r k) / g.eval (r k)
  have hb : Filter.Tendsto b Filter.atTop (nhds (-(c : ℂ))) := by
    have he : -B.eval 0 / g.eval 0 = -(c : ℂ) := by rw [hB]; field_simp
    rw [← he]
    exact hD.neg.div hG hg
  have hbre : Filter.Tendsto (fun k => (b k).re) Filter.atTop (nhds (-c)) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp hb
  have hs : ∀ᶠ k in Filter.atTop, (0 < (b k).re ↔ c < 0) := by
    rcases lt_or_gt_of_ne hc with hc | hc
    · filter_upwards [hbre.eventually_const_lt (neg_pos.mpr hc)] with k hk
      simp [hc, hk]
    · filter_upwards [hbre.eventually_lt_const (neg_neg_of_pos hc)] with k hk
      simp [not_lt.mpr hc.le, not_lt.mpr hk.le]
  filter_upwards [hs, hG.eventually_ne hg] with k hk hgk
  have he := hroot k
  simp only [IsRoot, eval_add, eval_mul, eval_X, eval_C] at he
  have heq : r k = (t k : ℂ) * b k := by
    dsimp [b]
    rw [← mul_div_assoc]
    apply (eq_div_iff hgk).mpr
    dsimp only [Function.comp_apply]
    linear_combination he
  rw [heq]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_pos_iff_of_pos_left (ht k)] using hk

private theorem regionCount_X_mul (g : ℂ[X]) (hg : g.eval 0 ≠ 0) (c : ℝ) :
    regionCount (X * g) (fun z => (z = 0 ∧ c < 0) ∨ 0 < z.re) =
      rightCount (X * g) + if c < 0 then 1 else 0 := by
  classical
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg
  rw [rightCount_mul X_ne_zero hg0, rightCount_X, zero_add]
  have hfilter : regionCount g (fun z => (z = 0 ∧ c < 0) ∨ 0 < z.re) = rightCount g := by
    unfold regionCount rightCount
    congr 1
    refine @Multiset.filter_congr ℂ (fun z => (z = 0 ∧ c < 0) ∨ 0 < z.re)
      (fun z => 0 < z.re) (fun _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) g.roots ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hh
      subst z
      exact hg ((mem_roots hg0).mp hz)
    simp [hz0]
  have hmul (p q : ℂ[X]) (hp : p ≠ 0) (hq : q ≠ 0) (W : ℂ → Prop) :
      regionCount (p * q) W = regionCount p W + regionCount q W := by
    simp only [regionCount, roots_mul (mul_ne_zero hp hq), Multiset.filter_add, Multiset.card_add]
  rw [hmul X g X_ne_zero hg0, hfilter]
  have hx : regionCount (X : ℂ[X]) (fun z => (z = 0 ∧ c < 0) ∨ 0 < z.re) =
      if c < 0 then 1 else 0 := by
    unfold regionCount
    rw [roots_X, Multiset.filter_singleton]
    by_cases hc : c < 0 <;> simp [hc]
  rw [hx, Nat.add_comm]

/-- Count the root crossing at a simple zero of the limiting polynomial.
The other imaginary-axis multiplicities stay fixed. This is the analytic
endpoint argument used after reversing a degree-reducing Routh step. -/
theorem rightCount_affine_simple_zero (g B : ℂ[X]) (hg : g.eval 0 ≠ 0)
    (c : ℝ) (hc : c ≠ 0) (hB : B.eval 0 = (c : ℂ) * g.eval 0)
    (n : ℕ) (hp : ∀ t : unitInterval, X * g + C (t : ℂ) * B ≠ 0)
    (hd : ∀ t : unitInterval, (X * g + C (t : ℂ) * B).natDegree = n)
    (haxis : ∀ (t : unitInterval) z, z.re = 0 → z ≠ 0 →
      (X * g + C (t : ℂ) * B).rootMultiplicity z = (X * g).rootMultiplicity z) :
    rightCount (X * g + B) = rightCount (X * g) + if c < 0 then 1 else 0 := by
  have hzero (t : ℝ) (ht : 0 < t) : (X * g + C (t : ℂ) * B).eval 0 ≠ 0 := by
    simpa [hB] using mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) hg)
  have hcount (t : unitInterval) (ht : (0 : ℝ) < t) :
      rightCount (X * g + C (t : ℂ) * B) = rightCount (X * g + B) := by
    let a (x : unitInterval) : unitInterval :=
      ⟨t + (1 - (t : ℝ)) * x, by
        have ht0 := t.property.1
        have ht1 := t.property.2
        have hx0 := x.property.1
        have hx1 := x.property.2
        constructor <;> nlinarith⟩
    have ha (x : unitInterval) : (0 : ℝ) < a x := by
      have ht1 := t.property.2
      have hx0 := x.property.1
      dsimp [a]
      nlinarith
    have hcoeff (i : ℕ) : Continuous (fun x : unitInterval =>
        (X * g + C (a x : ℂ) * B).coeff i) := by
      simp only [coeff_add, coeff_C_mul]
      dsimp [a]
      fun_prop
    have hm (x : unitInterval) : axisCount (X * g + C (a x : ℂ) * B) =
        axisCount (X * g + B) := by
      apply axisCount_eq_of_rootMultiplicity
      intro z hz
      by_cases hz0 : z = 0
      · subst z
        rw [rootMultiplicity_eq_zero (hzero (a x) (ha x))]
        exact (rootMultiplicity_eq_zero (by simpa using hzero 1 (by norm_num))).symm
      · rw [haxis (a x) z hz hz0]
        simpa using (haxis 1 z hz hz0).symm
    have hh := rightCount_eq_of_connected_axisCount
      (fun x : unitInterval => X * g + C (a x : ℂ) * B) n (axisCount (X * g + B))
      (fun x => hp (a x)) (fun x => hd (a x)) hcoeff hm 0 1
    simpa [a] using hh
  let e (k : ℕ) : unitInterval := ⟨1 / ((k : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  have hepos (k : ℕ) : (0 : ℝ) < e k := by dsimp [e]; positivity
  have helim : Filter.Tendsto (fun k => (e k : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heC : Filter.Tendsto (fun k => (e k : ℂ)) Filter.atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp helim
  have hcoeff (i : ℕ) : Continuous (fun t : unitInterval =>
      (X * g + C (t : ℂ) * B).coeff i) := by
    simp only [coeff_add, coeff_C_mul]
    fun_prop
  obtain ⟨M, hM⟩ := exists_uniform_root_bound
    (fun t : unitInterval => X * g + C (t : ℂ) * B) n hp hd hcoeff
  have hA : X * g ≠ 0 := by simpa using hp 0
  have hAd : (X * g).natDegree = n := by simpa using hd 0
  rw [← regionCount_X_mul g hg c]
  refine regionCount_of_root_limits (fun k => X * g + C (e k : ℂ) * B)
    (X * g) n (rightCount (X * g + B)) _ (fun k => hp (e k)) hA
    (fun k => hd (e k)) hAd ?_ M (fun k => hM (e k)) (fun k => hcount (e k) (hepos k)) ?_
  · intro i
    simp only [coeff_add, coeff_C_mul]
    simpa using (heC.mul_const (B.coeff i)).const_add ((X * g).coeff i)
  · intro φ hφ r z hz hroot hlim
    by_cases hz0 : z = 0
    · subst z
      simpa using affine_zero_root_sign g B hg c hc hB
        (fun k => (e (φ k) : ℝ)) (fun k => hepos (φ k)) r hlim hroot
    simp only [hz0, false_and, false_or]
    have hreal : Filter.Tendsto (fun k => (r k).re) Filter.atTop (nhds z.re) :=
      Complex.continuous_re.continuousAt.tendsto.comp hlim
    rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
    · filter_upwards [hreal.eventually_lt_const hneg] with k hk
      simp [not_lt.mpr hk.le, not_lt.mpr hneg.le]
    · have hdiv : (X - C z) ^ (X * g).rootMultiplicity z ∣ B := by
        have ha := (X * g).pow_rootMultiplicity_dvd z
        have hb := (X * g + B).pow_rootMultiplicity_dvd z
        have he : (X * g + B).rootMultiplicity z = (X * g).rootMultiplicity z := by
          simpa using haxis 1 z hzero hz0
        rw [he] at hb
        simpa using dvd_sub hb ha
      have hh := affine_root_eventually_eq (X * g) B hA z hdiv
        (fun k => (e (φ k) : ℂ)) r (heC.comp hφ.tendsto_atTop) hlim hroot
      filter_upwards [hh] with k hk
      simp [hk, hzero]
    · filter_upwards [hreal.eventually_const_lt hpos] with k hk
      simp [hk, hpos]

end Polynomial
