module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Nilpotent
public import SympyProofs.LinearAlgebra.MatrixLogarithm.InvariantSubspaces
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Exponentials of finite-dimensional endomorphisms

Transport the analytic exponential along the equivalence with continuous linear
maps. Intertwining allows these results to be used on invariant subspaces.
The algebraic subspace results are in `MatrixLogarithm.InvariantSubspaces`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Exponential

variable [FiniteDimensional ℂ V]

local instance : CompleteSpace V := FiniteDimensional.complete ℂ V

noncomputable def endExp (f : End ℂ V) : End ℂ V :=
  (End.toContinuousLinearMap V).symm
    (NormedSpace.exp (End.toContinuousLinearMap V f))

theorem hasSum_endExp_apply (f : End ℂ V) (x : V) :
    HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (f ^ k) x) (endExp f x) := by
  have h := (ContinuousLinearMap.apply ℂ V x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (End.toContinuousLinearMap V f))
  simp only [ContinuousLinearMap.apply_apply, smul_apply, ← map_pow] at h
  change HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (f ^ k) x) (endExp f x) at h
  exact h

section Intertwining

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem endExp_intertwine {f : End ℂ V} {g : End ℂ W} (u : V →ₗ[ℂ] W)
    (h : g ∘ₗ u = u ∘ₗ f) : endExp g ∘ₗ u = u ∘ₗ endExp f := by
  ext x
  have hp (k : ℕ) : (g ^ k) (u x) = u ((f ^ k) x) :=
    congrArg (fun t : V →ₗ[ℂ] W => t x) (End.commute_pow_left_of_commute h k)
  have hs := (hasSum_endExp_apply f x).map u u.continuous_of_finiteDimensional
  exact (hasSum_endExp_apply g (u x)).unique (by simpa [Function.comp_def, hp] using hs)

end Intertwining

theorem endExp_add_of_commute (f g : End ℂ V) (h : Commute f g) :
    endExp (f + g) = endExp f * endExp g := by
  let := NormedAlgebra.restrictScalars ℚ ℂ (V →L[ℂ] V)
  apply (End.toContinuousLinearMap V).injective
  simpa only [endExp, map_add, map_mul, AlgEquiv.apply_symm_apply] using
    NormedSpace.exp_add_of_commute (h.map (End.toContinuousLinearMap V))

theorem endExp_smul_one (z : ℂ) :
    endExp (z • (1 : End ℂ V)) = Complex.exp z • 1 := by
  apply (End.toContinuousLinearMap V).injective
  simpa only [endExp, map_smul, map_one, AlgEquiv.apply_symm_apply,
    Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ] using
    (NormedSpace.algebraMap_exp_comm (𝔸 := V →L[ℂ] V) z).symm

theorem endExp_natCast_smul (f : End ℂ V) (k : ℕ) :
    endExp ((k : ℂ) • f) = endExp f ^ k := by
  let := NormedAlgebra.restrictScalars ℚ ℂ (V →L[ℂ] V)
  apply (End.toContinuousLinearMap V).injective
  simpa only [endExp, map_smul, map_pow, AlgEquiv.apply_symm_apply,
    Nat.cast_smul_eq_nsmul, map_nsmul] using
    NormedSpace.exp_nsmul k (End.toContinuousLinearMap V f)

theorem mem_spectrum_endExp (f : End ℂ V) {z : ℂ} (hz : z ∈ spectrum ℂ f) :
    Complex.exp z ∈ spectrum ℂ (endExp f) := by
  have h := spectrum.exp_mem_exp (End.toContinuousLinearMap V f)
    (z := z) (by simpa only [AlgEquiv.spectrum_eq] using hz)
  simpa only [endExp, AlgEquiv.spectrum_eq, ← Complex.exp_eq_exp_ℂ] using h

end Exponential

section NilpotentExponential

variable [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem endExp_eq_of_nilpotent {f : End ℂ V} (hf : IsNilpotent f) :
    endExp f = IsNilpotent.exp f := by
  apply (End.toContinuousLinearMap V).injective
  rw [endExp, AlgEquiv.apply_symm_apply, IsNilpotent.map_exp hf]
  exact Nilpotent.normedSpace_exp_eq (hf.map _)

end NilpotentExponential

end SympyProofs.MatrixExponential
