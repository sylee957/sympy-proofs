module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.LeadingStep

/-! The polynomial solver represents all bounded solutions, including the homogeneous
solutions and the combinations arising only after extension of the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- A polynomial has no coefficient at or above the cutoff, including at cutoff zero. -/
def Below {F : Type} [Semiring F] (m : ℕ) (p : Polynomial F) : Prop :=
  ∀ j ≥ m, p.coeff j = 0

theorem below_zero_iff {F : Type} [Semiring F] (p : Polynomial F) : Below 0 p ↔ p = 0 := by
  constructor
  · intro h
    ext j
    exact (h j (Nat.zero_le _)).trans (coeff_zero _).symm
  · rintro rfl j _
    exact coeff_zero _

/-- The final column span consists of exactly the old parameter directions admitting a
polynomial correction of the given degree bound. -/
theorem mem_descend_iff {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (a b : Poly (K R n)) (w d m : ℕ) (ha : a.natDegree ≤ d)
    (hb : b.natDegree ≤ d) (hab : a.coeff d = 0 → b.coeff d ≠ 0) (vs : List (Column R n))
    (out : State k n w) :
    out ∈ Submodule.span k (Column.value k w '' {v |
        v ∈ descend t.D (g.velocity t.D) a b lower w d m vs}) ↔
      ∃ (z : State k n w) (q : Polynomial (M k n)),
        z ∈ Submodule.span k (Column.value k w '' {v | v ∈ vs}) ∧ Below m q ∧
        z.2.2 = operator k t g a b q ∧ out = (z.1, z.2.1 + q, 0) := by
  let L := operator k t g a b
  induction m generalizing vs with
  | zero =>
    rw [descend, mem_restrict_iff]
    change (_ ∧ Below 0 out.2.2) ↔ _
    simp only [below_zero_iff]
    constructor
    · rintro ⟨hv,h₀⟩
      refine ⟨out,0,hv,rfl,by simpa using h₀, ?_⟩
      rw [add_zero, ← h₀]
    · rintro ⟨z,_,hz,rfl,h₀,rfl⟩
      rw [map_zero] at h₀
      rw [add_zero]
      have eqn : (z.1, z.2.1, (0 : Polynomial (M k n))) = z := by rw [← h₀]
      rw [eqn]
      exact ⟨hz,h₀⟩
  | succ i ih =>
    rw [descend]
    refine (ih (leadingStep t.D (g.velocity t.D) a b lower w d i vs)).trans ?_
    constructor
    · rintro ⟨v,p,hv,hp,hres,rfl⟩
      obtain ⟨z,c,hz,_,rfl⟩ := (mem_leadingStep_iff k hl g a b w d i vs hab v).mp hv
      change z.2.2 - L (monomial i c) = L p at hres
      refine ⟨z, monomial i c + p, hz, ?_, ?_, ?_⟩
      · intro j hj
        simp [coeff_monomial, hp j (by omega), show i ≠ j by omega]
      · change z.2.2 = L _
        rw [map_add]
        linear_combination hres
      · change (z.1, z.2.1 + monomial i c + p, (0 : Polynomial (M k n))) = _
        rw [add_assoc]
    · rintro ⟨z,q,hz,hq,hr,rfl⟩
      let c := q.coeff i
      let p := q - monomial i c
      let v := extendMap k w i L (z,c)
      have hv : v ∈ Submodule.span k (Column.value k w '' {v |
          v ∈ leadingStep t.D (g.velocity t.D) a b lower w d i vs}) := by
        apply (mem_leadingStep_iff k hl g a b w d i vs hab _).mpr
        refine ⟨z,c,hz,?_,rfl⟩
        rw [hr]
        exact (operator_top k t g a b d i ha hb q
          (natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => hq j (by omega)))).symm
      refine ⟨v,p,hv,?_,?_,?_⟩
      · intro j hj
        rcases hj.eq_or_lt with rfl | hj
        · simp [p,c]
        · simp [p, coeff_monomial, hq j (by omega), hj.ne]
      · change z.2.2 - L _ = L (q - _)
        rw [map_sub, hr]
      · change (z.1, z.2.1+q, (0 : Polynomial (M k n))) =
          (z.1, z.2.1 + monomial i c + (q - monomial i c), 0)
        abel

end SympyProofs.Calculus.Antiderivative.Solve
