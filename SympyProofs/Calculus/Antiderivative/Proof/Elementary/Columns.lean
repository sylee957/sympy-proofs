module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Initial

/-! Exact forms of the fields in a finished column of polynomial integration. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Largest input coefficient count, with zero for an empty input list. -/
abbrev size (ps : List (Poly (K R n))) := (ps.map (·.coeffs.length)).max?.getD 0

/-- The degree cutoff used for the numerator of the polynomial primitive. -/
abbrev bound (g : ReducedGen (K R n)) (ps : List (Poly (K R n))) :=
  degreeCutoff g (size ps)

/-- The final columns before their remaining constant coefficients are sent to the lower level. -/
abbrev polynomialColumns (t : Tower R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (s : ℕ) (ps : List (Poly (K R n))) :=
  coefficients t.D lower (g.velocity t.D) ps.length s (bound g ps) (initial ps)

/-- Combinations of the input polynomials satisfy the same common degree bound. -/
theorem accumulate_below (ps : List (Poly (K R n))) (x : Fin ps.length → k) :
    Below (size ps) (Linear.accumulate ps (modelPoly k) x) := by
  intro j hj
  rw [Linear.accumulate_apply, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hlen : (ps.get i).coeffs.length ≤ j :=
    (List.le_max?_getD_of_mem (List.mem_map_of_mem (f := fun p : Poly (K R n) =>
      p.coeffs.length) (ps.get_mem i))).trans hj
  have hv : (ps.get i).coeff j = 0 := by
    rw [Poly.coeff_eq_getD_coeffs]
    exact Poly.Raw.coeff_eq_zero_of_length_le hlen
  rw [AddMonoidAlgebra.coeff_smul_apply, modelPoly, coeff_map, Poly.coeff_equiv, hv, map_zero,
    smul_zero]

/-- The final column span represents exactly the partial solutions of the input combinations
whose residual is supported only at the reserved power. -/
theorem mem_polynomialColumns_iff {t : Tower R n} {lower : Level R n}
    (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (s : ℕ) (ps : List (Poly (K R n))) (z : State k n ps.length) :
    z ∈ Submodule.span k (Column.value k ps.length '' {v | v ∈ polynomialColumns t g lower s ps}) ↔
      Below (bound g ps) z.2.1 ∧ z.2.1.coeff s = 0 ∧
        z.2.2 = Linear.accumulate ps (modelPoly k) z.1 - laurentOp k t g s z.2.1 ∧
        z.2.2 = monomial s (z.2.2.coeff s) := by
  rw [polynomialColumns, mem_coefficients_iff k hl]
  constructor
  · rintro ⟨u,q,hu,hq,hs,rfl,h⟩
    obtain ⟨hu₀,huP⟩ := (mem_initial_iff k ps u).mp hu
    change Below _ (u.2.1+q) ∧ _ ∧ _ ∧ _
    simp only [hu₀, zero_add, huP] at h ⊢
    refine ⟨hq,hs,trivial,?_⟩
    let p := Linear.accumulate ps (modelPoly k) u.1
    change p - laurentOp k t g s q = monomial s ((p - laurentOp k t g s q).coeff s)
    ext j
    by_cases hj : j = s
    · subst j
      simp
    · rw [coeff_monomial_of_ne _ hj]
      by_cases hj' : j < bound g ps
      · exact h j hj' hj
      · have hm : size ps ≤ bound g ps := by cases g <;> simp [bound, degreeCutoff]
        have hp := accumulate_below k ps u.1 j (by omega)
        rw [coeff_sub, laurentOp_below k t g s _ q hq j (by omega)]
        simpa [p] using hp
  · rintro ⟨hb,hs,he,hr⟩
    refine ⟨(z.1,0,Linear.accumulate ps (modelPoly k) z.1), z.2.1,
      (mem_initial_iff k ps _).mpr ⟨rfl,rfl⟩, hb,hs,?_,?_⟩
    · simp only [zero_add]
      exact Prod.ext rfl (Prod.ext rfl he)
    · intro j _ hj
      rw [hr, coeff_monomial_of_ne _ hj]

end SympyProofs.Calculus.Antiderivative.Elementary
