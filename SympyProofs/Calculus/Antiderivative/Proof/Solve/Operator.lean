module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.ParameterStep
public import SympyProofs.Calculus.Antiderivative.Proof.PolynomialDerivation
public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants

/-! Linear operators on polynomial candidates and their effect on solution columns. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

/-- Original parameters, a partial polynomial solution and its remaining right-hand side. -/
abbrev State (n width : ℕ) := (Fin width → k) × Polynomial (M k n) × Polynomial (M k n)

private theorem deriv_smul (t : Tower R n) (g : ReducedGen (K R n)) (c : k)
    (p : Polynomial (M k n)) :
    t.polyDerModel k g (c • p) = c • t.polyDerModel k g p := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have h (q : Polynomial (M k n)) : c • q = Polynomial.C (Model.C k n c) * q := by
    rw [Algebra.smul_def]
    rfl
  rw [h, h, Derivation.leibniz]
  have dc : t.polyDerModel k g (Polynomial.C (Model.C k n c)) = 0 := by
    change Differential.implicitDeriv _ _ = _
    rw [Differential.implicitDeriv_C]
    change Polynomial.C (t.modelD k (Model.C k n c)) = _
    rw [Tower.modelD_C, map_zero]
  rw [dc, smul_zero, add_zero, smul_eq_mul]

/-- The cleared differential operator on polynomial numerators is linear over constants. -/
noncomputable def operator (t : Tower R n) (g : ReducedGen (K R n)) (a b : Poly (K R n)) :
    Polynomial (M k n) →ₗ[k] Polynomial (M k n) where
  toFun p := modelPoly k a * t.polyDerModel k g p + modelPoly k b * p
  map_add' p q := by simp [mul_add]; abel
  map_smul' c p := by simp [deriv_smul, smul_add]

/-- Update a column by giving its polynomial solution one arbitrary model coefficient. -/
noncomputable def extendMap (w i : ℕ) (L : Polynomial (M k n) →ₗ[k] Polynomial (M k n)) :
    State k n w × M k n →ₗ[k] State k n w where
  toFun v := (v.1.1, v.1.2.1 + monomial i v.2, v.1.2.2 - L (monomial i v.2))
  map_add' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · change _ + monomial i (p.2+q.2) = _
      rw [map_add]
      change (p.1.2.1 + q.1.2.1) + _ = (p.1.2.1 + _) + (q.1.2.1 + _)
      abel
    · change _ - L (monomial i (p.2+q.2)) = _
      rw [map_add, map_add]
      change (p.1.2.2+q.1.2.2) - _ = (p.1.2.2 - _) + (q.1.2.2 - _)
      abel
  map_smul' c p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · change c • p.1.2.1 + monomial i (c • p.2) = c • (p.1.2.1 + monomial i p.2)
      rw [smul_add, smul_monomial]
    · change c • p.1.2.2 - L (monomial i (c • p.2)) = c • (p.1.2.2 - L (monomial i p.2))
      rw [smul_sub, ← smul_monomial, map_smul]

theorem value_extend (t : Tower R n) (g : ReducedGen (K R n)) (a b : Poly (K R n))
    (w i : ℕ) (v : Column R n) (h : K R n) :
    (extend t.D (g.velocity t.D) a b i v h).value k w =
      extendMap k w i (operator k t g a b) (v.value k w, val k h) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · simp [extend, Column.value, modelPoly, extendMap]
  · change modelPoly k (v.residual - (a * Step.polyDer t.D _ (Poly.monomial i h) +
        b * Poly.monomial i h)) = modelPoly k v.residual - _
    change Step.modelPoly (val k) _ = Step.modelPoly (val k) v.residual - _
    rw [map_sub, map_add, map_mul, map_mul, Tower.modelPoly_polyDer]
    simp [operator, Step.modelPoly_apply, modelPoly]

end SympyProofs.Calculus.Antiderivative.Solve
