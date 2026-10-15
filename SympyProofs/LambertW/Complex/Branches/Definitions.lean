import SympyProofs.LambertW.Complex.Branches.Basic

/-! # Integer-indexed Lambert W branches

Index `-(n+1)` is normalized at `r = 3π/2 + 2πn` by the value `-ri`.
Index `n+1` uses the conjugate value `ri`. Index zero uses `W(e) = 1`.
The common analytic domain is the slit plane; values on the cut are unspecified.
-/
namespace LambertW.Complex
open Set ComplexConjugate

noncomputable def branchRadius (n : ℕ) : ℝ := 3 * Real.pi / 2 + 2 * Real.pi * n

theorem branchRadius_pos (n : ℕ) : 0 < branchRadius n := by
  unfold branchRadius
  positivity

noncomputable def negativeBranchValue (n : ℕ) : ℂ := -(branchRadius n : ℂ) * Complex.I

theorem exp_negativeBranchValue (n : ℕ) : Complex.exp (negativeBranchValue n) = Complex.I := by
  have he : negativeBranchValue n = (Real.pi : ℂ) / 2 * Complex.I -
      2 * Real.pi * Complex.I - n * (2 * Real.pi * Complex.I) := by
    unfold negativeBranchValue branchRadius
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_sub, Complex.exp_pi_div_two_mul_I,
    Complex.exp_two_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I]
  simp

theorem mulExp_negativeBranchValue (n : ℕ) :
    mulExp (negativeBranchValue n) = (branchRadius n : ℂ) := by
  unfold mulExp
  rw [exp_negativeBranchValue]
  unfold negativeBranchValue
  calc
    -(branchRadius n : ℂ) * Complex.I * Complex.I =
        -(branchRadius n : ℂ) * (Complex.I * Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

noncomputable def negativeBranchSeed (n : ℕ) : BranchSeed where
  input := branchRadius n
  input_pos := branchRadius_pos n
  value := negativeBranchValue n
  inverse := mulExp_negativeBranchValue n

noncomputable def positiveBranchSeed (n : ℕ) : BranchSeed where
  input := branchRadius n
  input_pos := branchRadius_pos n
  value := conj (negativeBranchValue n)
  inverse := by rw [mulExp_conj, mulExp_negativeBranchValue]; simp

noncomputable def zeroBranchSeed : BranchSeed where
  input := Real.exp 1
  input_pos := Real.exp_pos _
  value := 1
  inverse := by simp [mulExp]

/-- Exact normalization selecting each integer index. -/
noncomputable def branchSeed : ℤ → BranchSeed
  | .ofNat 0 => zeroBranchSeed
  | .ofNat (n + 1) => positiveBranchSeed n
  | .negSucc n => negativeBranchSeed n

/-- Integer-indexed Lambert W on the common slit domain. -/
noncomputable def branch (k : ℤ) : ℂ → ℂ := (branchSeed k).inverseFun

theorem analyticOnNhd_branch (k : ℤ) : AnalyticOnNhd ℂ (branch k) branchDomain :=
  (branchSeed k).analytic

@[simp] theorem branch_at_seed (k : ℤ) :
    branch k (branchSeed k).input = (branchSeed k).value := (branchSeed k).at_input

theorem mulExp_branch (k : ℤ) {z : ℂ} (hz : z ∈ branchDomain) :
    mulExp (branch k z) = z := (branchSeed k).right_inverse hz

theorem eqOn_branch (k : ℤ) {W : ℂ → ℂ} (ha : AnalyticOnNhd ℂ W branchDomain)
    (hb : W (branchSeed k).input = (branchSeed k).value)
    (hi : ∀ z ∈ branchDomain, mulExp (W z) = z) : EqOn W (branch k) branchDomain :=
  (branchSeed k).eqOn ha hb hi

theorem hasDerivAt_branch (k : ℤ) {z : ℂ} (hz : z ∈ branchDomain) :
    HasDerivAt (branch k) (Complex.exp (branch k z) * (1 + branch k z))⁻¹ z :=
  (branchSeed k).hasDerivAt hz

theorem deriv_branch (k : ℤ) {z : ℂ} (hz : z ∈ branchDomain) :
    deriv (branch k) z = (Complex.exp (branch k z) * (1 + branch k z))⁻¹ :=
  (hasDerivAt_branch k hz).deriv

theorem injOn_branch (k : ℤ) : InjOn (branch k) branchDomain := (branchSeed k).injOn

theorem continuousOn_branch (k : ℤ) : ContinuousOn (branch k) branchDomain :=
  fun z hz => (analyticOnNhd_branch k z hz).continuousAt.continuousWithinAt

@[simp] theorem branch_negSucc_base (n : ℕ) :
    branch (Int.negSucc n) (branchRadius n) = negativeBranchValue n :=
  branch_at_seed (Int.negSucc n)

@[simp] theorem branch_natSucc_base (n : ℕ) :
    branch (Int.ofNat (n + 1)) (branchRadius n) = conj (negativeBranchValue n) :=
  branch_at_seed (Int.ofNat (n + 1))

/-- Continuous paths have a unique lift initialized on the selected indexed branch. -/
theorem existsUnique_branch_path_lift (k : ℤ) {γ : unitInterval → ℂ}
    (hγ : Continuous γ) (hdom : ∀ t, γ t ∈ branchDomain) :
    ∃! F : unitInterval → ℂ, Continuous F ∧ F 0 = branch k (γ 0) ∧
      ∀ t, mulExp (F t) = γ t := by
  have hc : Continuous (fun t => branch k (γ t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticOnNhd_branch k _ (hdom t)).continuousAt.comp hγ.continuousAt)
  refine ⟨fun t => branch k (γ t), ⟨hc, rfl, fun t => mulExp_branch k (hdom t)⟩, ?_⟩
  intro F hF
  exact eq_of_middle_path_lifts hF.1 hc hF.2.2
    (fun t => mulExp_branch k (hdom t))
    (fun t => branchDomain_ne_criticalValue (hdom t)) hF.2.1

end LambertW.Complex
