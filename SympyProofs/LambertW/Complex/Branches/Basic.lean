import SympyProofs.LambertW.Complex.Middle.GlobalInverse

/-! # Normalized analytic Lambert inverses on the slit plane

A value above a positive real input selects a unique analytic inverse.
This construction is independent of the integer indexing convention.
-/
namespace LambertW.Complex
open Set Filter Topology

def branchDomain : Set ℂ := Complex.slitPlane

theorem branchDomain_ne_criticalValue {z : ℂ} (hz : z ∈ branchDomain) :
    z ≠ -Complex.exp (-1) := by
  intro he
  have hc : -Complex.exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) := by simp
  rw [he, hc] at hz
  have := Complex.ofReal_mem_slitPlane.mp hz
  linarith [Real.exp_pos (-1)]

/-- A normalization at a positive input. -/
structure BranchSeed where
  input : ℝ
  input_pos : 0 < input
  value : ℂ
  inverse : mulExp value = (input : ℂ)

namespace BranchSeed

theorem mem_domain (s : BranchSeed) : (s.input : ℂ) ∈ branchDomain :=
  Complex.ofReal_mem_slitPlane.mpr s.input_pos

theorem exists_inverse (s : BranchSeed) :
    ∃ W : ℂ → ℂ, AnalyticOnNhd ℂ W branchDomain ∧ W s.input = s.value ∧
      ∀ z ∈ branchDomain, mulExp (W z) = z :=
  exists_analytic_inverse_on_starDomain Complex.isOpen_slitPlane
    (Complex.starConvex_ofReal_slitPlane s.input_pos) s.mem_domain
    (fun _ hz => Complex.slitPlane_ne_zero hz)
    (fun _ hz => branchDomain_ne_criticalValue hz) s.inverse

noncomputable def inverseFun (s : BranchSeed) : ℂ → ℂ := s.exists_inverse.choose

theorem analytic (s : BranchSeed) : AnalyticOnNhd ℂ s.inverseFun branchDomain :=
  s.exists_inverse.choose_spec.1

@[simp] theorem at_input (s : BranchSeed) : s.inverseFun s.input = s.value :=
  s.exists_inverse.choose_spec.2.1

theorem right_inverse (s : BranchSeed) {z : ℂ} (hz : z ∈ branchDomain) :
    mulExp (s.inverseFun z) = z := s.exists_inverse.choose_spec.2.2 z hz

/-- Normalization uniquely determines the inverse on the slit plane. -/
theorem eqOn (s : BranchSeed) {W : ℂ → ℂ} (hW : AnalyticOnNhd ℂ W branchDomain)
    (hb : W s.input = s.value) (hi : ∀ z ∈ branchDomain, mulExp (W z) = z) :
    Set.EqOn W s.inverseFun branchDomain := by
  have hp : IsPreconnected branchDomain :=
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  let : PreconnectedSpace branchDomain := Subtype.preconnectedSpace hp
  have hc (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F branchDomain) :
      Continuous (fun t : branchDomain => F t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hF _ t.property).continuousAt.comp continuous_subtype_val.continuousAt)
  have he := eq_of_continuous_mulExp_lifts (hc W hW) (hc s.inverseFun s.analytic)
    (fun t => (hi _ t.property).trans (s.right_inverse t.property).symm)
    (fun t => by rw [hi _ t.property]; exact branchDomain_ne_criticalValue t.property)
    (t₀ := ⟨s.input, s.mem_domain⟩) (hb.trans s.at_input.symm)
  exact fun z hz => congrFun he ⟨z, hz⟩

theorem hasDerivAt (s : BranchSeed) {z : ℂ} (hz : z ∈ branchDomain) :
    HasDerivAt s.inverseFun (Complex.exp (s.inverseFun z) * (1 + s.inverseFun z))⁻¹ z := by
  have hd := (s.analytic z hz).differentiableAt
  have he : deriv s.inverseFun z =
      (Complex.exp (s.inverseFun z) * (1 + s.inverseFun z))⁻¹ := by
    apply deriv_of_eventually_mulExp_eq hd
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with y hy
    exact s.right_inverse hy
  rw [← he]
  exact hd.hasDerivAt

theorem injOn (s : BranchSeed) : Set.InjOn s.inverseFun branchDomain := by
  intro x hx y hy he
  simpa only [s.right_inverse hx, s.right_inverse hy] using congrArg mulExp he

end BranchSeed
end LambertW.Complex
