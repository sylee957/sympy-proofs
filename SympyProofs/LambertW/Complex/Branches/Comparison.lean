import SympyProofs.LambertW.Complex.Branches.Definitions
import SympyProofs.LambertW.Complex.Principal.Analytic

/-! # Compatibility of the indexed family with existing Lambert branches -/
namespace LambertW.Complex
open Set

theorem branchDomain_subset_principalDomain : branchDomain ⊆ principalDomain := by
  intro z hz
  rcases hz with hz | hz
  · right; have := Real.exp_pos (-1); linarith
  · exact Or.inl hz

/-- Index zero is the restriction of the principal branch to the common slit domain. -/
theorem branch_zero_eq_principal {z : ℂ} (hz : z ∈ branchDomain) :
    branch 0 z = principal z := by
  have ha : AnalyticOnNhd ℂ principal branchDomain :=
    fun _ hy => analyticAt_principal (branchDomain_subset_principalDomain hy)
  have hb : principal (branchSeed 0).input = (branchSeed 0).value := by
    change principal (Real.exp 1 : ℂ) = 1
    have hm : (1 : ℂ) ∈ principalRange := by
      simpa using (ofReal_mem_principalRange (1 : ℝ)).mpr (by norm_num)
    simpa [mulExp] using principal_mulExp hm
  exact (eqOn_branch 0 ha hb (fun _ hy =>
    mulExp_principal (branchDomain_subset_principalDomain hy)) hz).symm

theorem eqOn_branch_zero_principal : EqOn (branch 0) principal branchDomain :=
  fun _ hz => branch_zero_eq_principal hz

end LambertW.Complex
