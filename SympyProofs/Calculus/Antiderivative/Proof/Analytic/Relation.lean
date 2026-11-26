module

public import SympyProofs.Calculus.Antiderivative.Proof.Poles

/-! An admissible primitive has no positive-degree monic differential eigenpolynomial.
For an admissible exponential every such polynomial is a power of the generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} {t : Tower R n} {k : Type} [Field k] [CharZero k] [Algebra R k]
variable [FaithfulSMul R k]

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

theorem monic_relation {g : ReducedGen (K R n)} (hg : g.Admissible k t) {p : (M k n)[X]}
    (hp : p.Monic) (hd : 0 < p.natDegree)
    (h : t.polyDerModel k g p = C ((p.natDegree : M k n) * val k ((g.velocity t.D).coeff 1)) * p) :
    ∃ u, g = .exp u ∧ p = X ^ p.natDegree := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have hv (g : ReducedGen (K R n)) :
      val k ((g.velocity t.D).coeff 1) = (t.modelVelocity k g).coeff 1 := by
    rw [← modelPoly_velocity k t g]
    simp
  rw [hv] at h
  cases g with
  | prim b =>
    have e : Extension.affine 0 (val k b) p = 0 := by
      simpa [polyDerModel, modelVelocity, Extension.affine] using h
    have ec := congrArg (fun q : (M k n)[X] => q.coeff (p.natDegree - 1)) e
    simp only [Extension.coeff_affine, Nat.sub_add_cancel hd, coeff_natDegree, hp.leadingCoeff,
      coeff_zero, mul_one, mul_zero, zero_mul, add_zero] at ec
    exfalso
    apply hg
    refine ⟨-(p.coeff (p.natDegree - 1)) / (p.natDegree : M k n), ?_⟩
    rw [Derivation.leibniz_div_const _ _ _ (Derivation.map_natCast ..), smul_eq_mul,
      inv_mul_eq_div, map_neg, div_eq_iff (Nat.cast_ne_zero.mpr hd.ne')]
    linear_combination -ec
  | exp u =>
    refine ⟨u,rfl,?_⟩
    have e : Extension.affine (val k (t.D u)) 0 p = C ((p.natDegree : M k n) * val k (t.D u)) * p := by
      simpa [polyDerModel, modelVelocity, Extension.affine] using h
    ext i
    rw [coeff_X_pow]
    rcases lt_trichotomy i p.natDegree with hi | rfl | hi
    · rw [ite_eq_right hi.ne]
      by_contra hn
      apply hg
      refine ⟨p.natDegree-i,p.coeff i,by omega,hn,(div_eq_iff hn).mpr ?_⟩
      have ec := congrArg (fun q : (M k n)[X] => q.coeff i) e
      simp only [Extension.coeff_affine, coeff_C_mul, mul_zero, zero_mul, add_zero] at ec
      rw [Nat.cast_sub hi.le]
      change Differential.deriv _ = _
      linear_combination ec
    · simp [hp.coeff_natDegree]
    · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']

end SympyProofs.Calculus.Antiderivative.Tower
