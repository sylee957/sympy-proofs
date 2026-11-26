module

public import SympyProofs.Calculus.Antiderivative.Proof.PolynomialDerivation
public import SympyProofs.Calculus.Antiderivative.Spec.Admissible
import Mathlib.Tactic.LinearCombination

/-! The normal primes of an admissible primitive or exponential extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

omit [CharZero k] in
/-- A prime dividing its differential derivative becomes an eigenvector after normalization. -/
private theorem monic_special (t : Tower R n) (g : ReducedGen (K R n)) {p : (M k n)[X]}
    (hp : Prime p) (hs : p ∣ t.polyDerModel k g p) :
    let m := p * C p.leadingCoeff⁻¹
    t.polyDerModel k g m = C ((m.natDegree : M k n) * val k ((g.velocity t.D).coeff 1)) * m := by
  let m := p * C p.leadingCoeff⁻¹
  have hm : m.Monic := monic_mul_leadingCoeff_inv hp.ne_zero
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hmp : m ∣ p := ⟨C p.leadingCoeff, by simp [m, mul_assoc, ← C_mul, hc]⟩
  have hmd : p ∣ t.polyDerModel k g m := by
    rw [show m = _ from rfl, Derivation.leibniz]
    exact dvd_add (dvd_mul_right _ _) (hs.mul_left _)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt
    (dvd_sub (hmp.trans hmd) (dvd_mul_left m _)) (degree_polyDerModel k t g hm))

/-- Every prime in the newest primitive generator is normal. -/
theorem prime_normal_prim (t : Tower R n) (b : K R n) (ha : (ReducedGen.prim b).Admissible k t)
    {p : (M k n)[X]} (hp : Prime p) : ¬ p ∣ t.polyDerModel k (.prim b) p := by
  intro hs
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let m := p * C p.leadingCoeff⁻¹
  have hm : m.Monic := monic_mul_leadingCoeff_inv hp.ne_zero
  have hpos : 0 < m.natDegree := by
    simpa [m, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))] using
      hp.irreducible.natDegree_pos
  have he := monic_special k t (.prim b) hp hs
  change t.polyDerModel k (.prim b) m = _ at he
  have hvel : val k (((ReducedGen.prim b).velocity t.D).coeff 1) = 0 := by
    have h := congrArg (fun p : (M k n)[X] => p.coeff 1) (modelPoly_velocity k t (.prim b))
    simpa [modelVelocity, ReducedGen.velocity] using h
  rw [hvel, mul_zero, C_0, zero_mul] at he
  have hz : Extension.affine 0 (val k b) m = 0 := by
    simpa [polyDerModel, modelVelocity, Gen.velocity, Extension.affine] using he
  have h := congrArg (fun s : (M k n)[X] => s.coeff (m.natDegree - 1)) hz
  simp only [Extension.coeff_affine, Nat.sub_add_cancel hpos, coeff_natDegree, hm.leadingCoeff,
    coeff_zero, mul_one, mul_zero, zero_mul, add_zero] at h
  apply ha
  refine ⟨-(m.coeff (m.natDegree - 1)) / (m.natDegree : M k n), ?_⟩
  rw [Derivation.leibniz_div_const _ _ _ (Derivation.map_natCast ..), smul_eq_mul,
    inv_mul_eq_div, map_neg, div_eq_iff (Nat.cast_ne_zero.mpr hpos.ne')]
  linear_combination -h

/-- At an exponential step only the newest indeterminate can be a special prime. -/
theorem prime_normal_exp (t : Tower R n) (u : K R n) (ha : (ReducedGen.exp u).Admissible k t)
    {p : (M k n)[X]} (hp : Prime p) (h0 : p.coeff 0 ≠ 0) :
    ¬ p ∣ t.polyDerModel k (.exp u) p := by
  intro hs
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let m := p * C p.leadingCoeff⁻¹
  have hc := inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero)
  have hpos : 0 < m.natDegree := by simpa [m, natDegree_mul_C hc] using hp.irreducible.natDegree_pos
  have he := monic_special k t (.exp u) hp hs
  change t.polyDerModel k (.exp u) m = _ at he
  have hvel : val k (((ReducedGen.exp u).velocity t.D).coeff 1) = val k (t.D u) := by
    have h := congrArg (fun p : (M k n)[X] => p.coeff 1) (modelPoly_velocity k t (.exp u))
    simpa [modelVelocity, ReducedGen.velocity] using h
  rw [hvel] at he
  have he' : Extension.affine (val k (t.D u)) 0 m = C ((m.natDegree : M k n) * val k (t.D u)) * m := by
    simpa [polyDerModel, modelVelocity, Gen.velocity, Extension.affine] using he
  have h := congrArg (fun s : (M k n)[X] => s.coeff 0) he'
  have hm0 : m.coeff 0 ≠ 0 := by simpa [m] using mul_ne_zero h0 hc
  apply ha
  refine ⟨m.natDegree, m.coeff 0, hpos, hm0, (div_eq_iff hm0).mpr ?_⟩
  change Differential.deriv (m.coeff 0) = _
  simpa [Extension.coeff_affine] using h

end SympyProofs.Calculus.Antiderivative.Tower
