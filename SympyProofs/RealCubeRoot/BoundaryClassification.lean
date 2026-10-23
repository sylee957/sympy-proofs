module

public import SympyProofs.RealCubeRoot.Boundary
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Classification of continuous one-sided boundary extensions

An extension that respects conjugation, is continuous along the imaginary axis,
and takes a one-sided limit at every cut point must be `cubicSurdRight` or `cubicSurdLeft`.
The side is allowed to depend on the point in the hypotheses; the conclusion
shows that continuity and conjugation force a single global convention.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Filter Set
open scoped ComplexConjugate Topology

/-- There exists exactly one real branch continuous on the closed right half-plane. -/
theorem existsUnique_cubicSurdRight :
    ∃! f : ℂ → ℂ, IsRealBranch f ∧ ContinuousOn f {z : ℂ | 0 ≤ z.re} := by
  exact ⟨cubicSurdRight, ⟨isRealBranch_cubicSurdRight, continuousOn_cubicSurdRight_closedHalfPlane⟩,
    fun _ hf => unique_cubicSurdRight hf.1 hf.2⟩

/-- There exists exactly one real branch continuous on the closed left half-plane. -/
theorem existsUnique_cubicSurdLeft :
    ∃! f : ℂ → ℂ, IsRealBranch f ∧ ContinuousOn f {z : ℂ | z.re ≤ 0} := by
  exact ⟨cubicSurdLeft, ⟨isRealBranch_cubicSurdLeft, continuousOn_cubicSurdLeft_closedHalfPlane⟩,
    fun _ hf => unique_cubicSurdLeft hf.1 hf.2⟩

/-- Continuous cube roots on a connected set, with nonzero values, are fixed by
one value. Their quotient is a continuous function into the finite cube roots of one. -/
theorem eqOn_of_cube_eq_of_continuous_eq_at {U : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hcube : ∀ z ∈ U, f z ^ 3 = g z ^ 3) (hne : ∀ z ∈ U, g z ≠ 0)
    {a : ℂ} (ha : a ∈ U) (heq : f a = g a) : EqOn f g U := by
  have hfinite : Set.Finite {w : ℂ | w ^ 3 = 1} := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using
      (Polynomial.finite_setOfPred_isRoot
        (Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 3) (1 : ℂ)))
  have hmaps : MapsTo (fun z => f z / g z) U {w : ℂ | w ^ 3 = 1} := by
    intro z hz
    change (f z / g z) ^ 3 = 1
    rw [div_pow, hcube z hz, div_self (pow_ne_zero 3 (hne z hz))]
  intro z hz
  have h := hU.constant_of_mapsTo hfinite.isDiscrete (hf.div hg hne) hmaps hz ha
  simpa [heq, div_self (hne a ha), div_eq_one_iff_eq (hne z hz)] using h

/-- For total cube roots extending the same branch and respecting conjugation,
continuity along the axis makes the value at `I` determine the entire extension. -/
theorem eq_of_cube_of_continuousOn_axis_of_eq_at_I {f g : ℂ → ℂ}
    (heq : EqOn f g domain)
    (hf_cube : ∀ z, f z ^ 3 = z) (hg_cube : ∀ z, g z ^ 3 = z)
    (hf_conj : ∀ z, f (conj z) = conj (f z))
    (hg_conj : ∀ z, g (conj z) = conj (g z))
    (hf_cont : ContinuousOn f {z : ℂ | z.re = 0})
    (hg_cont : ContinuousOn g {z : ℂ | z.re = 0})
    (hI : f I = g I) : f = g := by
  have hconv : Convex ℝ {z : ℂ | z.re = 0} :=
    convex_hyperplane (.mk add_re smul_re) 0
  have hupper : EqOn f g {z : ℂ | z.re = 0 ∧ 0 < z.im} := by
    apply eqOn_of_cube_eq_of_continuous_eq_at
      (hconv.inter (convex_halfSpace_im_gt 0)).isPreconnected
      (hf_cont.mono (fun _ hz => hz.1)) (hg_cont.mono (fun _ hz => hz.1))
      (fun z _ => (hf_cube z).trans (hg_cube z).symm) ?_ (a := I) (by simp) hI
    intro z hz hzero
    have hz0 : z = 0 := by simpa [hzero] using (hg_cube z).symm
    simp [hz0] at hz
  funext z
  by_cases hz : z.re = 0
  · by_cases hz0 : z = 0
    · exact heq (Or.inr hz0)
    by_cases him : 0 < z.im
    · exact hupper ⟨hz, him⟩
    have hneg : z.im < 0 := by
      have hne : z.im ≠ 0 := fun h => hz0 (Complex.ext hz h)
      exact lt_of_le_of_ne (le_of_not_gt him) hne
    have h := congrArg conj (hupper (x := conj z) (by simpa using And.intro hz hneg))
    simpa only [hf_conj, hg_conj, conj_conj] using h
  · exact heq (Or.inl hz)

/-- A right-hand limit of an extension of the fixed branch has only one possible value. -/
theorem eq_cubicSurdRight_of_tendsto_from_right {f : ℂ → ℂ} (hf : IsRealBranch f)
    {z : ℂ} (hz : z.re = 0)
    (hlim : Tendsto f (𝓝[{w : ℂ | 0 < w.re}] z) (𝓝 (f z))) :
    f z = cubicSurdRight z := by
  have : NeBot (𝓝[{w : ℂ | 0 < w.re}] z) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_setOfPred_lt_re]
      exact hz.ge)
  have heq : EqOn f cubicSurdRight {w : ℂ | 0 < w.re} :=
    fun w hw => hf.eqOn isRealBranch_cubicSurdRight (Or.inl (ne_of_gt hw))
  exact tendsto_nhds_unique hlim
    ((tendsto_cubicSurdRight_from_right hz).congr' heq.eventuallyEq_nhdsWithin.symm)

/-- A left-hand limit of an extension of the fixed branch has only one possible value. -/
theorem eq_cubicSurdLeft_of_tendsto_from_left {f : ℂ → ℂ} (hf : IsRealBranch f)
    {z : ℂ} (hz : z.re = 0)
    (hlim : Tendsto f (𝓝[{w : ℂ | w.re < 0}] z) (𝓝 (f z))) :
    f z = cubicSurdLeft z := by
  have : NeBot (𝓝[{w : ℂ | w.re < 0}] z) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_setOfPred_re_lt]
      exact hz.le)
  have heq : EqOn f cubicSurdLeft {w : ℂ | w.re < 0} :=
    fun w hw => hf.eqOn isRealBranch_cubicSurdLeft (Or.inl (ne_of_lt hw))
  exact tendsto_nhds_unique hlim
    ((tendsto_cubicSurdLeft_from_left hz).congr' heq.eventuallyEq_nhdsWithin.symm)

/-- The side may initially vary with the cut point. Axis continuity and global
conjugation symmetry will force it to be the same everywhere. -/
structure IsOneSidedExtension (f : ℂ → ℂ) : Prop where
  branch : IsRealBranch f
  conjugation : ∀ z, f (conj z) = conj (f z)
  continuous_axis : ContinuousOn f {z : ℂ | z.re = 0}
  one_sided : ∀ z : ℂ, z.re = 0 →
    Tendsto f (𝓝[{w : ℂ | 0 < w.re}] z) (𝓝 (f z)) ∨
    Tendsto f (𝓝[{w : ℂ | w.re < 0}] z) (𝓝 (f z))

theorem isOneSidedExtension_cubicSurdRight : IsOneSidedExtension cubicSurdRight where
  branch := isRealBranch_cubicSurdRight
  conjugation := cubicSurdRight_conj
  continuous_axis := continuousOn_cubicSurdRight_axis
  one_sided _ hz := Or.inl (tendsto_cubicSurdRight_from_right hz)

theorem isOneSidedExtension_cubicSurdLeft : IsOneSidedExtension cubicSurdLeft where
  branch := isRealBranch_cubicSurdLeft
  conjugation := cubicSurdLeft_conj
  continuous_axis := continuousOn_cubicSurdLeft_axis
  one_sided _ hz := Or.inr (tendsto_cubicSurdLeft_from_left hz)

/-- On the axis, one-sided limits select one of the two boundary values. -/
theorem IsOneSidedExtension.eq_right_or_left_at {f : ℂ → ℂ}
    (hf : IsOneSidedExtension f) {z : ℂ} (hz : z.re = 0) :
    f z = cubicSurdRight z ∨ f z = cubicSurdLeft z :=
  (hf.one_sided z hz).imp (eq_cubicSurdRight_of_tendsto_from_right hf.branch hz)
    (eq_cubicSurdLeft_of_tendsto_from_left hf.branch hz)

/-- The cube equation on the cut follows from the one-sided limits. -/
theorem IsOneSidedExtension.cube {f : ℂ → ℂ} (hf : IsOneSidedExtension f)
    (z : ℂ) : f z ^ 3 = z := by
  by_cases hz : z.re = 0
  · rcases hf.eq_right_or_left_at hz with h | h
    · rw [h, cubicSurdRight_cube]
    · rw [h, cubicSurdLeft_cube]
  · exact hf.branch.cube z (Or.inl hz)

/-- Classification: the hypotheses permit exactly the right and left extensions. -/
theorem IsOneSidedExtension.eq_right_or_left {f : ℂ → ℂ}
    (hf : IsOneSidedExtension f) : f = cubicSurdRight ∨ f = cubicSurdLeft := by
  rcases hf.eq_right_or_left_at (z := I) (by simp) with h | h
  · exact Or.inl (eq_of_cube_of_continuousOn_axis_of_eq_at_I
      (hf.branch.eqOn isRealBranch_cubicSurdRight) hf.cube cubicSurdRight_cube
      hf.conjugation cubicSurdRight_conj hf.continuous_axis continuousOn_cubicSurdRight_axis h)
  · exact Or.inr (eq_of_cube_of_continuousOn_axis_of_eq_at_I
      (hf.branch.eqOn isRealBranch_cubicSurdLeft) hf.cube cubicSurdLeft_cube
      hf.conjugation cubicSurdLeft_conj hf.continuous_axis continuousOn_cubicSurdLeft_axis h)

theorem isOneSidedExtension_iff {f : ℂ → ℂ} :
    IsOneSidedExtension f ↔ f = cubicSurdRight ∨ f = cubicSurdLeft := by
  constructor
  · exact IsOneSidedExtension.eq_right_or_left
  · rintro (rfl | rfl)
    · exact isOneSidedExtension_cubicSurdRight
    · exact isOneSidedExtension_cubicSurdLeft

end RealCubeRoot
