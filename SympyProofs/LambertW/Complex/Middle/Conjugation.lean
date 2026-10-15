import SympyProofs.LambertW.Complex.Middle.Global
import SympyProofs.LambertW.Complex.Principal.Conjugation

/-! # Conjugation symmetry of the analytic real-lower extension -/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

@[simp] theorem conj_mem_middleDomain (z : ℂ) :
    conj z ∈ middleDomain ↔ z ∈ middleDomain := by
  simp [middleDomain]

/-- Reflection across the real axis preserves the double-cut middle branch. -/
theorem middle_conj {z : ℂ} (hz : z ∈ middleDomain) :
    middle (conj z) = conj (middle z) := by
  let : PreconnectedSpace middleDomain := Subtype.preconnectedSpace
    ((starConvex_middleDomain middleBase_mem).isPathConnected
      (ofReal_mem_middleDomain.mpr middleBase_mem)).isConnected.isPreconnected
  have hF : Continuous (fun t : middleDomain => middle (conj (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((analyticOnNhd_middle _ ((conj_mem_middleDomain _).mpr t.property)).continuousAt.comp
      Complex.continuous_conj.continuousAt).comp continuous_subtype_val.continuousAt
  have hG : Continuous (fun t : middleDomain => conj (middle (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact Complex.continuous_conj.continuousAt.comp
      ((analyticOnNhd_middle _ t.property).continuousAt.comp continuous_subtype_val.continuousAt)
  have hi (t : middleDomain) : mulExp (middle (conj (t : ℂ))) =
      mulExp (conj (middle (t : ℂ))) := by
    rw [mulExp_middle ((conj_mem_middleDomain _).mpr t.property), mulExp_conj,
      mulExp_middle t.property]
  have hn (t : middleDomain) : mulExp (middle (conj (t : ℂ))) ≠ -Complex.exp (-1) := by
    rw [mulExp_middle ((conj_mem_middleDomain _).mpr t.property)]
    exact middleDomain_ne_criticalValue ((conj_mem_middleDomain _).mpr t.property)
  have he := eq_of_continuous_mulExp_lifts hF hG hi hn
    (t₀ := ⟨(middleBase : ℂ), ofReal_mem_middleDomain.mpr middleBase_mem⟩)
    (by simp)
  exact congrFun he ⟨z, hz⟩

end LambertW.Complex
