import SympyProofs.LambertW.Complex.Principal.UpperUniqueness

/-!
# The principal complex Lambert W inverse on the slit domain

`principal` is uniquely specified on `principalDomain`, with values in
`principalRange`. Values on the removed ray, including the branch point,
are unspecified. Boundary extensions and analyticity are separate results.
-/

namespace LambertW.Complex

open Set ComplexConjugate

/-- The principal complex inverse on the open slit domain.
Outside `principalDomain`, the total function has unspecified values. -/
noncomputable def principal : ℂ → ℂ := Function.invFunOn mulExp principalRange

theorem principal_mem {z : ℂ} (hz : z ∈ principalDomain) :
    principal z ∈ principalRange :=
  Function.invFunOn_mem (existsUnique_principalRange_mulExp hz).exists

/-- The defining Lambert W equation throughout the principal slit domain. -/
theorem mulExp_principal {z : ℂ} (hz : z ∈ principalDomain) :
    mulExp (principal z) = z :=
  Function.invFunOn_eq (existsUnique_principalRange_mulExp hz).exists

theorem principal_mul_exp {z : ℂ} (hz : z ∈ principalDomain) :
    principal z * Complex.exp (principal z) = z := mulExp_principal hz

/-- The inverse also recovers every point in the principal output region. -/
theorem principal_mulExp {w : ℂ} (hw : w ∈ principalRange) :
    principal (mulExp w) = w :=
  mulExp_bijOn_principalDomain.injOn (Function.invFunOn_apply_mem hw) hw
    (Function.invFunOn_apply_eq hw)

/-- A solution in the principal region must be the selected principal value. -/
theorem eq_principal_of_mulExp_eq {w z : ℂ}
    (hw : w ∈ principalRange) (he : mulExp w = z) : w = principal z := by
  rw [← he, principal_mulExp hw]

@[simp] theorem principal_zero : principal 0 = 0 := by
  simpa using principal_mulExp zero_mem_principalRange

/-- Agreement with the real principal branch on the real part of the slit domain. -/
theorem principal_ofReal {x : ℝ} (hx : -Real.exp (-1) < x) :
    principal (x : ℂ) = (Real.principal x : ℂ) := by
  have hp : -1 < Real.principal x := by
    simpa using Real.strictMonoOn_principal
      (show -Real.exp (-1) ∈ Ici (-Real.exp (-1)) by simp) hx.le hx
  apply (eq_principal_of_mulExp_eq ((ofReal_mem_principalRange _).mpr hp) ?_).symm
  rw [mulExp_ofReal, Real.mulExp_principal hx.le]

/-- Conjugation symmetry on the principal slit domain. -/
theorem principal_conj {z : ℂ} (hz : z ∈ principalDomain) :
    principal (conj z) = conj (principal z) := by
  apply (eq_principal_of_mulExp_eq
    ((conj_mem_principalRange _).mpr (principal_mem hz)) ?_).symm
  rw [mulExp_conj, mulExp_principal hz]

theorem principal_bijOn : BijOn principal principalDomain principalRange :=
  mulExp_bijOn_principalDomain.symm mulExp_bijOn_principalDomain.invOn_invFunOn.symm

end LambertW.Complex
