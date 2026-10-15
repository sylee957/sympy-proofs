import SympyProofs.LambertW.Complex.Branches.Definitions

/-! # Conjugate pairs of nonprincipal indexed branches -/
namespace LambertW.Complex
open Set ComplexConjugate

@[simp] theorem conj_mem_branchDomain (z : ℂ) :
    conj z ∈ branchDomain ↔ z ∈ branchDomain := by
  simp [branchDomain, Complex.slitPlane]

/-- Positive and negative indexed branches are conjugate on the slit plane. -/
theorem branch_natSucc_conj (n : ℕ) {z : ℂ} (hz : z ∈ branchDomain) :
    branch (Int.ofNat (n + 1)) (conj z) = conj (branch (Int.negSucc n) z) := by
  let : PreconnectedSpace branchDomain := Subtype.preconnectedSpace
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hF : Continuous (fun t : branchDomain => branch (Int.ofNat (n + 1)) (conj (t : ℂ))) :=
    continuous_iff_continuousAt.mpr (fun t =>
      ((analyticOnNhd_branch _ _ ((conj_mem_branchDomain _).mpr t.property)).continuousAt.comp
        Complex.continuous_conj.continuousAt).comp continuous_subtype_val.continuousAt)
  have hG : Continuous (fun t : branchDomain => conj (branch (Int.negSucc n) (t : ℂ))) :=
    continuous_iff_continuousAt.mpr (fun t =>
      Complex.continuous_conj.continuousAt.comp
        ((analyticOnNhd_branch _ _ t.property).continuousAt.comp continuous_subtype_val.continuousAt))
  have hi (t : branchDomain) :
      mulExp (branch (Int.ofNat (n + 1)) (conj (t : ℂ))) =
        mulExp (conj (branch (Int.negSucc n) (t : ℂ))) := by
    rw [mulExp_branch _ ((conj_mem_branchDomain _).mpr t.property), mulExp_conj,
      mulExp_branch _ t.property]
  have hn (t : branchDomain) :
      mulExp (branch (Int.ofNat (n + 1)) (conj (t : ℂ))) ≠ -Complex.exp (-1) := by
    rw [mulExp_branch _ ((conj_mem_branchDomain _).mpr t.property)]
    exact branchDomain_ne_criticalValue ((conj_mem_branchDomain _).mpr t.property)
  have he := eq_of_continuous_mulExp_lifts hF hG hi hn
    (t₀ := ⟨(branchRadius n : ℂ), Complex.ofReal_mem_slitPlane.mpr (branchRadius_pos n)⟩)
    (by
      change branch (Int.ofNat (n + 1)) (conj (branchRadius n : ℂ)) =
        conj (branch (Int.negSucc n) (branchRadius n))
      rw [Complex.conj_ofReal, branch_natSucc_base, branch_negSucc_base])
  exact congrFun he ⟨z, hz⟩

end LambertW.Complex
