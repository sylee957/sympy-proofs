module

public import SympyProofs.LinearAlgebra.MatrixFunction.Primary
public import SympyProofs.LinearAlgebra.MatrixPower.Local
public import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenEndomorphism

/-!
# Complex powers by primary functional calculus

The construction applies to every finite complex endomorphism. It retains
nilpotent Jordan data, agrees with every natural power, and agrees with the
half-open logarithm power on invertible endomorphisms.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

noncomputable def endCpow (f : End ℂ V) (z : ℂ) : End ℂ V :=
  primaryFunction f (fun a => localCpowPolynomial a z (Module.finrank ℂ V + 1))

theorem endCpow_intertwine (f : End ℂ V) (z a : ℂ) (ha : a ∈ spectrum ℂ f) :
    endCpow f z ∘ₗ (f.maxGenEigenspace a).subtype =
      (f.maxGenEigenspace a).subtype ∘ₗ
        aeval (primaryEnd f a) (localCpowPolynomial a z (Module.finrank ℂ V + 1)) :=
  primaryFunction_intertwine f _ a ha

variable [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V]

theorem endCpow_natCast (f : End ℂ V) (k : ℕ) : endCpow f (k : ℂ) = f ^ k := by
  symm
  apply primaryFunction_unique
  intro a ha
  rw [aeval_localCpowPolynomial_natCast _ _ _ _
    ((Submodule.finrank_le _).trans (Nat.le_succ _))
    (pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
      (nilpotent_pow_finrank (primaryEnd_nilpotent f a)))]
  exact End.commute_pow_left_of_commute (primaryEnd_intertwine f a) k

theorem endCpow_eq_exp_logInterpolation (f : End ℂ V) (z : ℂ) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ f,
      (X - C a) ^ (Module.finrank ℂ V + 1) ∣ p - localLogPolynomial a (Module.finrank ℂ V + 1))
    (hf : ∀ a ∈ spectrum ℂ f, a ≠ 0) :
    endCpow f z = endExp (z • aeval f p) := by
  symm
  apply primaryFunction_unique
  intro a ha
  have hn := pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
    (nilpotent_pow_finrank (primaryEnd_nilpotent f a))
  rw [aeval_localCpowPolynomial_of_ne_zero _ _ _ _
    ((Submodule.finrank_le _).trans (Nat.le_succ _)) (hf a ha) hn]
  apply endExp_intertwine
  rw [LinearMap.smul_comp, LinearMap.comp_smul,
    aeval_intertwine _ (primaryEnd_intertwine f a)]
  congr 2
  exact aeval_eq_of_dvd_sub _ a _ (hp a ha)
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hn)

/-- Agreement with any logarithm satisfying the half-open spectral condition. -/
theorem endCpow_eq_exp_of_halfOpenLogarithm (f l : End ℂ V) (z : ℂ)
    (hf : IsUnit f) (hl : endExp l = f) (hs : spectrum ℂ l ⊆ halfOpenStrip) :
    endCpow f z = endExp (z • l) := by
  obtain ⟨p, hp⟩ := exists_logInterpolation f.finite_spectrum (Module.finrank ℂ V + 1)
  have he := logInterpolation_endExp_halfOpen l _ (Nat.le_succ _) p (by rwa [hl]) hs
  rw [hl] at he
  rw [← he]
  apply endCpow_eq_exp_logInterpolation f z p hp
  intro a ha hzero
  subst a
  exact spectrum.zero_notMem ℂ hf ha

end SympyProofs.MatrixExponential
