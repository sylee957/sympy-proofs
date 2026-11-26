module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Leading

/-! Exact image of one leading-coefficient elimination, in both the algebraic and the
differential cases. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The selected residual coefficient divided by its leading multiplier. -/
private noncomputable def residualQuotient (w j : ℕ) (s : M k n) : State k n w →ₗ[k] M k n where
  toFun z := z.2.2.coeff j / s
  map_add' x y := by change (x.2.2+y.2.2).coeff j / s = _; rw [coeff_add, add_div]
  map_smul' c x := by
    change (c • x.2.2).coeff j / s = c • (x.2.2.coeff j / s)
    rw [AddMonoidAlgebra.coeff_smul_apply, div_eq_mul_inv, div_eq_mul_inv, smul_mul_assoc]

private theorem combination_quotient (w j : ℕ) (vs : List (Column R n)) (r : K R n)
    (p : Fin vs.length → k) : Model.linearCombination k (List.ofFn p)
      (vs.map fun v => v.residual.coeff j / r) =
        (Linear.accumulate vs (Column.value k w) p).2.2.coeff j / val k r := by
  rw [residual_coeff, linearCombination_ofFn, linearCombination_ofFn]
  simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- The span after eliminating one leading coefficient allows exactly the extensions of the
previous space satisfying that coefficient's equation. -/
theorem mem_leadingStep_iff {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (a b : Poly (K R n)) (w d i : ℕ) (vs : List (Column R n))
    (hab : a.coeff d = 0 → b.coeff d ≠ 0) (out : State k n w) :
    out ∈ Submodule.span k (Column.value k w '' {c |
        c ∈ leadingStep t.D (g.velocity t.D) a b lower w d i vs}) ↔
      ∃ (z : State k n w) (c : M k n), z ∈ Submodule.span k (Column.value k w '' {v | v ∈ vs}) ∧
        val k (a.coeff d) * t.modelD k c +
          val k (b.coeff d + (i : K R n) * (g.velocity t.D).coeff 1 * a.coeff d) * c =
            z.2.2.coeff (d+i) ∧ extendMap k w i (operator k t g a b) (z,c) = out := by
  let r := a.coeff d
  let s := b.coeff d + (i : K R n) * (g.velocity t.D).coeff 1 * r
  let E := extendMap k w i (operator k t g a b)
  change _ ↔ ∃ z c, _ ∧ val k r * t.modelD k c + val k s * c = _ ∧ E (z,c) = out
  by_cases he : r = 0
  · have h₀ : val k s ≠ 0 := (_root_.map_ne_zero _).mpr (by simpa [s,he] using hab he)
    let T := E.comp ((LinearMap.id (R := k) (M := State k n w)).prod
      (residualQuotient k w (d+i) (val k s)))
    have hm (v : Column R n) :
        (extend t.D (g.velocity t.D) a b i v (v.residual.coeff (d+i) / s)).value
        k w = T (v.value k w) := by
      rw [value_extend]
      change E (v.value k w, val k (_ / _)) = E (v.value k w, _)
      rw [map_div₀]
      simp [residualQuotient, Column.value, modelPoly]
    rw [leadingStep, ite_eq_left he]
    change out ∈ Submodule.span k (Column.value k w '' {c | c ∈
      vs.map fun v => extend t.D (g.velocity t.D) a b i v (v.residual.coeff (d+i) / s)}) ↔ _
    rw [Linear.mem_mapped_columns_iff _ _ _ _ T (fun q _ => hm q)]
    simp only [he, map_zero, zero_mul, zero_add]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z, z.2.2.coeff (d+i) / val k s, hz, by field_simp, rfl⟩
    · rintro ⟨z,c,hz,hc,rfl⟩
      refine ⟨z,hz,?_⟩
      change E (z,z.2.2.coeff (d+i) / val k s) = E (z,c)
      rw [← hc, mul_div_cancel_left₀ _ h₀]
  · have hn : val k r ≠ 0 := (_root_.map_ne_zero _).mpr he
    rw [leadingStep]
    simp only [show a.coeff d ≠ 0 from he, ite_false]
    rw [mem_extendSolutions_iff k hl _ _ _ _ _ _ _ _ (List.length_map ..)]
    simp only [combination_quotient k w, map_div₀]
    constructor
    · rintro ⟨p,c,h,hout⟩
      refine ⟨_, c, (Linear.mem_columns_iff vs _ _).mpr ⟨p,rfl⟩, ?_, hout⟩
      change t.modelD k c + val k s / val k r * c = _ / val k r at h
      field_simp at h
      linear_combination h
    · rintro ⟨z,c,hz,h,hout⟩
      obtain ⟨p,rfl⟩ := (Linear.mem_columns_iff vs _ _).mp hz
      refine ⟨p,c,?_,hout⟩
      change t.modelD k c + val k s / val k r * c = _ / val k r
      field_simp
      linear_combination h

end SympyProofs.Calculus.Antiderivative.Solve
