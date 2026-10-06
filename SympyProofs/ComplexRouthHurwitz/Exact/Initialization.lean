import SympyProofs.ComplexRouthHurwitz.Exact.Coefficients
import SympyProofs.ComplexRouthHurwitz.Exact.Model.Initialization

/-! Normalized input and its complex interpretation for the integer-row runner. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial Model
noncomputable section
open Classical

namespace Proofs

def input (p : GaussianInt[X]) : Rows.Row (p.natDegree+1) :=
  Vector.ofFn (fun j => phase p.leadingCoeff * p.coeff j.val)

def rotated (p : GaussianInt[X]) : ℂ[X] :=
  C (FractionFree.phase (denote p).leadingCoeff) * denote p

theorem input_spec (p : GaussianInt[X]) (hp : p ≠ 0) :
    mapRow (input p) = Coefficients.pack (p.natDegree+1) (rotated p) ∧
    (rotated p).natDegree = p.natDegree ∧ 0 < (rotated p).leadingCoeff.re := by
  have hpn := denote_ne_zero p hp
  constructor
  · apply Vector.ext; intro j hj
    simp only [input, mapRow, Coefficients.pack, rotated, coeff_C_mul, denote, coeff_map,
      Fin.getElem_fin, Vector.getElem_ofFn, map_mul, map_phase]
    rw [Polynomial.leadingCoeff_map_of_injective GaussianInt.toComplex_injective]
  constructor
  · rw [rotated, natDegree_C_mul (FractionFree.phase_ne_zero _), denote_natDegree]
  · simp only [rotated, leadingCoeff_mul, leadingCoeff_C]
    exact FractionFree.phase_re_pos _ (leadingCoeff_ne_zero.mpr hpn)

theorem rotated_counts (p : GaussianInt[X]) :
    rightCount (rotated p) = rightCount (denote p) ∧
    axisCount (rotated p) = axisCount (denote p) :=
  counts_C_mul _ _ (FractionFree.phase_ne_zero _)
end Proofs

end
end RouthHurwitz.ComplexRouth.Exact.Gaussian
