module

public import SympyProofs.RealCubeRoot.Analytic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex

/-!
# Uniqueness on the two half-planes

Two analytic cube-root branches on a connected domain agree everywhere if they
agree at one point with nonzero value. On each of our two half-planes,
conjugation symmetry forces the value at `1` or `-1`, respectively, to be real.
The real cube root is unique, so these two normalizations determine the branch.

Uniqueness is stated on `domain`, including zero. Analyticity on
`analyticDomain` fixes both half-planes, and the cube equation fixes zero.
The nonzero imaginary-axis values remain unconstrained.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Set
open scoped ComplexConjugate

/-- A cube-root branch on `domain`, analytic on `analyticDomain` and respecting conjugation. -/
structure IsRealBranch (f : ℂ → ℂ) : Prop where
  cube : ∀ z ∈ domain, f z ^ 3 = z
  analytic : AnalyticOnNhd ℂ f analyticDomain
  conjugation : ∀ z ∈ domain, f (conj z) = conj (f z)

theorem isRealBranch_cubicSurd : IsRealBranch cubicSurd where
  cube _ hz := cubicSurd_cube hz
  analytic := analyticOnNhd_cubicSurd
  conjugation z _ := cubicSurd_conj z

/-- Conjugation symmetry forces a cube root of a real number to be its real root. -/
theorem eq_realCubicSurd_of_cube_of_conj {x : ℝ} {w : ℂ}
    (hcube : w ^ 3 = (x : ℂ)) (hconj : conj w = w) :
    w = (realCubicSurd x : ℂ) := by
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.mp hconj
  have hr : r ^ 3 = x := by exact_mod_cast hcube
  rw [realCubicSurd_unique hr]

/-- A general uniqueness lemma: one nonzero normalization fixes an analytic cube root
on any preconnected set. -/
theorem eqOn_of_cube_eq_of_eq_at {U : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hcube : ∀ z ∈ U, f z ^ 3 = g z ^ 3)
    {a : ℂ} (ha : a ∈ U) (heq : f a = g a) (hne : g a ≠ 0) :
    EqOn f g U := by
  have hp : ∀ z ∈ U,
      (f z - g z) * (f z ^ 2 + f z * g z + g z ^ 2) = 0 := by
    intro z hz
    linear_combination hcube z hz
  rcases (hf.sub hg).eq_zero_or_eq_zero_of_mul_eq_zero
      (((hf.pow 2).add (hf.mul hg)).add (hg.pow 2)) hp hU with h | h
  · exact fun z hz => sub_eq_zero.mp (h z hz)
  · have hzero : (3 : ℂ) * g a ^ 2 = 0 := by
      have h' := h a ha
      simp only [Pi.add_apply, Pi.pow_apply] at h'
      rw [heq] at h'
      linear_combination h'
    exact False.elim ((mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)) hzero)

/-- Analytic cube-root branches normalized at `1` and `-1` are unique on `domain`.
No conjugation assumption is needed once those two values are fixed. -/
theorem unique_of_normalized {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f analyticDomain)
    (hcube : ∀ z ∈ domain, f z ^ 3 = z)
    (hone : f 1 = 1) (hneg : f (-1) = -1) : EqOn f cubicSurd domain := by
  have hright : {z : ℂ | 0 < z.re} ⊆ analyticDomain := fun z hz => ne_of_gt hz
  have hleft : {z : ℂ | z.re < 0} ⊆ analyticDomain := fun z hz => ne_of_lt hz
  have hr : EqOn f cubicSurd {z : ℂ | 0 < z.re} :=
    eqOn_of_cube_eq_of_eq_at (convex_halfSpace_re_gt 0).isPreconnected
      (hf.mono hright) (analyticOnNhd_cubicSurd.mono hright)
      (fun z hz => (hcube z (analyticDomain_subset_domain (hright hz))).trans
        (cubicSurd_cube (analyticDomain_subset_domain (hright hz))).symm)
      (a := 1) (by simp) (by simpa using hone) (by simp)
  have hl : EqOn f cubicSurd {z : ℂ | z.re < 0} :=
    eqOn_of_cube_eq_of_eq_at (convex_halfSpace_re_lt 0).isPreconnected
      (hf.mono hleft) (analyticOnNhd_cubicSurd.mono hleft)
      (fun z hz => (hcube z (analyticDomain_subset_domain (hleft hz))).trans
        (cubicSurd_cube (analyticDomain_subset_domain (hleft hz))).symm)
      (a := -1) (by simp) (by simpa using hneg) (by simp)
  intro z hz
  rcases hz with hz | rfl
  · rcases lt_or_gt_of_ne hz with hz | hz
    · exact hl hz
    · exact hr hz
  · simpa only [cubicSurd_zero] using
      eq_zero_of_pow_eq_zero (hcube 0 zero_mem_domain)

/-- On this fixed domain, being an analytic cube root and commuting with
conjugation already determines the real branch uniquely. -/
theorem unique {f : ℂ → ℂ} (hf : IsRealBranch f) : EqOn f cubicSurd domain := by
  apply unique_of_normalized hf.analytic hf.cube
  · have hconj : conj (f 1) = f 1 := by
      simpa only [map_one] using (hf.conjugation 1 (by simp [domain])).symm
    have h := eq_realCubicSurd_of_cube_of_conj (hf.cube 1 (by simp [domain])) hconj
    norm_num [realCubicSurd] at h
    exact h
  · have hconj : conj (f (-1)) = f (-1) := by
      simpa only [map_neg, map_one] using (hf.conjugation (-1) (by simp [domain])).symm
    have h := eq_realCubicSurd_of_cube_of_conj (x := -1)
      (by simpa using hf.cube (-1) (by simp [domain])) hconj
    norm_num [realCubicSurd] at h ⊢
    exact h

/-- Any two branches satisfying the specification agree on the domain, including zero. -/
theorem IsRealBranch.eqOn {f g : ℂ → ℂ} (hf : IsRealBranch f) (hg : IsRealBranch g) :
    EqOn f g domain :=
  fun _ hz => (unique hf hz).trans (unique hg hz).symm

/-- Literal unique existence after restricting the functions to `domain`, including zero. -/
theorem existsUnique_restriction :
    ∃! r : domain → ℂ, ∃ f : ℂ → ℂ, IsRealBranch f ∧ r = (fun z : domain => f z) := by
  refine ⟨(fun z : domain => cubicSurd z),
    ⟨cubicSurd, isRealBranch_cubicSurd, rfl⟩, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  funext z
  exact unique hf z.property

end RealCubeRoot
