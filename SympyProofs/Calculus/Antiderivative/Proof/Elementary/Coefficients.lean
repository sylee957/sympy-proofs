module

public import SympyProofs.Calculus.Antiderivative.Program.Elementary
public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Descend

/-! The column space for polynomial integration, reserving the coefficient of the zeroth
Laurent power for elementary integration below. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The leading degree cutoff of the primitive numerator for either kind of generator. -/
abbrev degreeCutoff (g : ReducedGen (K R n)) (size : ℕ) :=
  match g with | .prim _ => size+1 | .exp _ => size

/-- The polynomial numerator of the derivative of `P / θ^s`. At a primitive step `s = 0`. -/
noncomputable abbrev laurentOp (t : Tower R n) (g : ReducedGen (K R n)) (s : ℕ) :=
  operator k t g 1 (Poly.C (-(s : K R n) * (g.velocity t.D).coeff 1))

theorem laurentOp_below (t : Tower R n) (g : ReducedGen (K R n)) (s m : ℕ)
    (p : Polynomial (M k n)) (hp : Below m p) : Below m (laurentOp k t g s p) := by
  cases m with
  | zero =>
    rw [below_zero_iff] at hp ⊢
    rw [hp, map_zero]
  | succ m =>
    have hn : p.natDegree ≤ m := natDegree_le_iff_coeff_eq_zero.mpr fun j hj => hp j hj
    intro j hj
    change (modelPoly k (1 : Poly (K R n)) * t.polyDerModel k g p +
      modelPoly k (Poly.C _) * p).coeff j = _
    have hc (c : K R n) : modelPoly k (Poly.C c) = Polynomial.C (val k c) := by simp [modelPoly]
    rw [show modelPoly k (1 : Poly (K R n)) = 1 by simp [modelPoly], one_mul, hc,
      coeff_add, coeff_C_mul, hp j hj, mul_zero, add_zero]
    exact coeff_eq_zero_of_natDegree_lt (by have := natDegree_der_le k t g p; omega)

theorem laurentOp_top (t : Tower R n) (g : ReducedGen (K R n)) (s i : ℕ)
    (p : Polynomial (M k n)) (hp : Below (i+1) p) :
    (laurentOp k t g s p).coeff i = t.modelD k (p.coeff i) +
      val k (((i : K R n)-(s : K R n)) * (g.velocity t.D).coeff 1) * p.coeff i := by
  have hc (x : K R n) : (Poly.C x).natDegree = 0 := by
    rw [← Poly.natDegree_equiv, Poly.equiv_C, natDegree_C]
  have hc₀ (x : K R n) : (Poly.C x).coeff 0 = x := by
    rw [← Poly.coeff_equiv, Poly.equiv_C, coeff_C_zero]
  have h₁ : (1 : Poly (K R n)).coeff 0 = 1 := by
    rw [← Poly.coeff_equiv, map_one, AddMonoidAlgebra.coeff_one_zero]
  have he := operator_top k t g 1 (Poly.C (-(s : K R n) * (g.velocity t.D).coeff 1)) 0 i
    (by rw [← Poly.natDegree_equiv]; simp) (le_of_eq (hc _)) p
    (natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => hp j hj))
  rw [Nat.zero_add, hc₀, h₁, map_one, one_mul, mul_one] at he
  rw [he]
  simp only [map_add, map_mul, map_neg, map_natCast, map_sub]
  ring

private theorem coeffStep_iff {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (s w i : ℕ) (vs : List (Column R n)) (out : State k n w) :
    let dx := g.velocity t.D
    out ∈ Submodule.span k (Column.value k w '' {v | v ∈
      extendSolutions t.D dx 1 (Poly.C (-(s : K R n)*dx.coeff 1)) lower w i vs
        (((i : K R n)-(s : K R n))*dx.coeff 1) (vs.map fun c => c.residual.coeff i)}) ↔
      ∃ (z : State k n w) (c : M k n), z ∈ Submodule.span k (Column.value k w '' {v | v ∈ vs}) ∧
        t.modelD k c + val k (((i : K R n)-(s : K R n))*dx.coeff 1)*c = z.2.2.coeff i ∧
          extendMap k w i (laurentOp k t g s) (z,c) = out := by
  dsimp only
  rw [mem_extendSolutions_iff k hl g _ _ w i vs _ _ (List.length_map ..)]
  constructor
  · rintro ⟨a,c,h,he⟩
    refine ⟨_, c, (Linear.mem_columns_iff vs _ _).mpr ⟨a,rfl⟩, ?_, he⟩
    rwa [residual_coeff k w vs a i]
  · rintro ⟨z,c,hz,h,he⟩
    obtain ⟨v,rfl⟩ := (Linear.mem_columns_iff vs _ z).mp hz
    exact ⟨v,c,h.trans (residual_coeff k w vs v i),he⟩

/-- Every linear combination output by the triangular coefficient solver represents an input
combination with all requested coefficients eliminated. Conversely, every polynomial correction
with that property is present, including after extending the constants. -/
theorem mem_coefficients_iff {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (w s m : ℕ) (vs : List (Column R n)) (out : State k n w) :
    out ∈ Submodule.span k (Column.value k w '' {v |
        v ∈ coefficients t.D lower (g.velocity t.D) w s m vs}) ↔
      ∃ (z : State k n w) (q : Polynomial (M k n)),
        z ∈ Submodule.span k (Column.value k w '' {v | v ∈ vs}) ∧ Below m q ∧ q.coeff s = 0 ∧
        out = (z.1, z.2.1+q, z.2.2 - laurentOp k t g s q) ∧
        ∀ j < m, j ≠ s → out.2.2.coeff j = 0 := by
  let L := laurentOp k t g s
  induction m generalizing vs with
  | zero =>
    simp only [coefficients, below_zero_iff, Nat.not_lt_zero, false_implies, implies_true, and_true]
    constructor
    · intro h
      exact ⟨out,0,h,rfl,by simp,by simp⟩
    · rintro ⟨z,_,hz,rfl,_,he⟩
      simp only [add_zero, map_zero, sub_zero, Prod.mk.eta] at he
      exact he ▸ hz
  | succ i ih =>
    rw [coefficients]
    by_cases hi : i = s
    · rw [ite_eq_left hi]
      refine (ih vs).trans ?_
      constructor
      · rintro ⟨z,q,hz,hq,hc,he,hh⟩
        exact ⟨z,q,hz,fun j hj => hq j (by omega),hc,he,fun j hj hne => hh j (by omega) hne⟩
      · rintro ⟨z,q,hz,hq,hc,he,hh⟩
        refine ⟨z,q,hz,fun j hj => ?_,hc,he,fun j hj => hh j (by omega)⟩
        rcases hj.eq_or_lt with rfl | hj
        · simpa [hi] using hc
        · exact hq _ hj
    · rw [ite_eq_right hi]
      refine (ih _).trans ?_
      constructor
      · rintro ⟨v,p,hv,hp,hps,hout,hvan⟩
        obtain ⟨z,c,hz,he,rfl⟩ := (coeffStep_iff k hl g s w i vs v).mp hv
        let q := monomial i c + p
        have hq : Below (i+1) q := by
          intro j hj
          simp [q, coeff_monomial, hp j (by omega), show i ≠ j by omega]
        have hqi : q.coeff i = c := by simp [q, hp i le_rfl]
        have hid : out = (z.1, z.2.1+q, z.2.2 - L q) := by
          rw [hout]
          change (z.1, z.2.1 + monomial i c + p, z.2.2 - L (monomial i c) - L p) = _
          simp only [q, map_add, add_assoc, sub_sub]
        refine ⟨z,q,hz,hq,by simp [q, coeff_monomial, hi, hps],hid,?_⟩
        intro j hj hne
        rcases Nat.lt_or_eq_of_le (by omega : j ≤ i) with hj | rfl
        · exact hvan j hj hne
        · rw [hid]
          change (z.2.2 - L q).coeff j = 0
          rw [coeff_sub, laurentOp_top k t g s j q hq, hqi, he, sub_self]
      · rintro ⟨z,q,hz,hq,hqs,hout,hvan⟩
        let c := q.coeff i
        let p := q - monomial i c
        let v := extendMap k w i L (z,c)
        have hp : Below i p := by
          intro j hj
          rcases hj.eq_or_lt with rfl | hj
          · simp [p,c]
          · simp [p, coeff_monomial, hq j (by omega), hj.ne]
        have he : t.modelD k c + val k (((i : K R n)-(s : K R n))*(g.velocity t.D).coeff 1)*c =
            z.2.2.coeff i := by
          have h := hvan i (by omega) hi
          rw [hout] at h
          change (z.2.2 - L q).coeff i = 0 at h
          rw [coeff_sub, laurentOp_top k t g s i q hq] at h
          exact (sub_eq_zero.mp h).symm
        refine ⟨v,p,(coeffStep_iff k hl g s w i vs v).mpr ⟨z,c,hz,he,rfl⟩,
          hp,by simp [p, coeff_monomial, hi, hqs],?_,fun j hj => hvan j (by omega)⟩
        rw [hout]
        change (_, z.2.1+q, z.2.2 - L q) =
          (_, z.2.1 + monomial i c + (q - monomial i c), z.2.2 - L (monomial i c) - L p)
        rw [show L p = L q - L (monomial i c) from map_sub ..]
        refine Prod.ext rfl (Prod.ext ?_ ?_) <;> abel

end SympyProofs.Calculus.Antiderivative.Elementary
