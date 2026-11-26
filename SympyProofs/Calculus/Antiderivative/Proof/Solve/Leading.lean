module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Extend

/-! The coefficient of the cleared differential equation at its highest possible power. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

theorem coeff_der (t : Tower R n) (g : ReducedGen (K R n)) (p : Polynomial (M k n)) (i : ℕ) :
    (t.polyDerModel k g p).coeff i = t.modelD k (p.coeff i) +
      (i : M k n) * val k ((g.velocity t.D).coeff 1) * p.coeff i +
      ((i+1 : ℕ) : M k n) * val k ((g.velocity t.D).coeff 0) * p.coeff (i+1) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let a := val k ((g.velocity t.D).coeff 1)
  let b := val k ((g.velocity t.D).coeff 0)
  have hv : t.modelVelocity k g = C a * X + C b := by
    have he (j : ℕ) : val k ((g.velocity t.D).coeff j) = (t.modelVelocity k g).coeff j := by
      rw [← Tower.modelPoly_velocity]
      simp
    cases g <;> simp [a, b, he, Tower.modelVelocity]
  have hh : t.polyDerModel k g = Extension.affine a b := by rw [Tower.polyDerModel, hv]
  rw [hh]
  exact Extension.coeff_affine a b p i

/-- An affine generator derivative never raises the degree of a polynomial. -/
theorem natDegree_der_le (t : Tower R n) (g : ReducedGen (K R n)) (p : Polynomial (M k n)) :
    (t.polyDerModel k g p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_der, coeff_eq_zero_of_natDegree_lt hj, coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

/-- The leading coefficient of the cleared equation gives the scalar differential equation
solved at index `i`. The candidate polynomial may have smaller degree. -/
theorem operator_top (t : Tower R n) (g : ReducedGen (K R n)) (a b : Poly (K R n)) (d i : ℕ)
    (ha : a.natDegree ≤ d) (hb : b.natDegree ≤ d) (p : Polynomial (M k n))
    (hp : p.natDegree ≤ i) :
    (operator k t g a b p).coeff (d+i) =
      val k (a.coeff d) * t.modelD k (p.coeff i) +
        val k (b.coeff d + (i : K R n) * (g.velocity t.D).coeff 1 * a.coeff d) * p.coeff i := by
  change (modelPoly k a * t.polyDerModel k g p + modelPoly k b * p).coeff (d+i) = _
  have ha' : (modelPoly k a).natDegree ≤ d := by simpa [modelPoly] using ha
  have hb' : (modelPoly k b).natDegree ≤ d := by simpa [modelPoly] using hb
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le ha' ((natDegree_der_le k t g p).trans hp),
    coeff_mul_add_eq_of_natDegree_le hb' hp, coeff_der,
    coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i+1)]
  simp [modelPoly]
  ring

end SympyProofs.Calculus.Antiderivative.Solve
