module

public import SympyProofs.Calculus.Antiderivative.Proof.SolveDegree
public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Initial

/-! The bounded coefficient algorithm gives the full graph of the polynomial equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Finite-vector and list presentations of the same model polynomial combination. -/
theorem accumulate_polynomial (ps : List (Poly (K R n))) (v : Fin ps.length → k) :
    Linear.accumulate ps (modelPoly k) v = Model.polynomialCombination k (List.ofFn v) ps := by
  rw [Linear.accumulate_apply]
  induction ps with
  | nil => simp [Model.polynomialCombination]
  | cons p ps ih =>
    simp only [List.length_cons] at v ⊢
    rw [Fin.sum_univ_succ, List.ofFn_succ]
    simp only [List.get_cons_zero, Model.polynomialCombination]
    exact congrArg₂ (· + ·) (by rw [Algebra.smul_def]; rfl) (ih fun i => v i.succ)

/-- A solution family, its polynomial values and its residual form the graph of the
cleared differential equation in the polynomial ring. -/
theorem polynomialSolutions_spec [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)]
    (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t) (L : Level R n)
    (hs : L.SolveSpec k t) (hlog : L.LogRelationsSpec k t)
    (a b : Poly (K R n)) (ha : a ≠ 0) (rhs : List (Poly (K R n))) (z : State k n rhs.length) :
    z ∈ Submodule.span k
      (Column.value k rhs.length '' {v | v ∈ polynomialSolutions t.D g L a b rhs}) ↔
      z.2.2 = 0 ∧ operator k t g a b z.2.1 = Linear.accumulate rhs (modelPoly k) z.1 := by
  let d := max a.natDegree b.natDegree
  let size := (rhs.map (·.coeffs.length)).max?.getD 0
  have hlead : a.coeff d = 0 → b.coeff d ≠ 0 := by
    intro h
    have hlt : a.natDegree < b.natDegree := by
      by_contra hn
      rw [show d = a.natDegree from max_eq_left (by omega)] at h
      exact Poly.leadingCoeff_ne_zero ha ((Poly.coeff_natDegree a).symm.trans h)
    have hb : b ≠ 0 := by rintro rfl; simp at hlt
    rw [show d = b.natDegree from max_eq_right hlt.le]
    rw [Poly.coeff_natDegree]
    exact Poly.leadingCoeff_ne_zero hb
  have hsize (v : Fin rhs.length → k) : Below size (Linear.accumulate rhs (modelPoly k) v) := by
    rw [accumulate_polynomial]
    intro j hj
    apply Model.polynomialCombination_coeff_high
    intro p hp
    exact (List.le_max?_getD_of_mem (List.mem_map_of_mem (f := fun p : Poly (K R n) =>
      p.coeffs.length) hp)).trans hj
  unfold polynomialSolutions
  rw [mem_descend_iff k hs g a b _ d _ (le_max_left ..) (le_max_right ..) hlead]
  simp only [mem_initial_iff]
  constructor
  · rintro ⟨v,q,⟨hv,hr⟩,_,he,rfl⟩
    exact ⟨rfl, by simpa [hv] using he.symm.trans hr⟩
  · rintro ⟨hz,he⟩
    have hout : Below size (operator k t g a b z.2.1) := he ▸ hsize _
    refine ⟨(z.1,0,Linear.accumulate rhs (modelPoly k) z.1),z.2.1,⟨rfl,rfl⟩,?_,he.symm,?_⟩
    · cases g with
      | prim v =>
        exact degree_prim k t v hg L hs a b d size (le_max_left ..) (le_max_right ..)
          hlead _ hout
      | exp u =>
        exact degree_exp k t u hg L hlog a b d size (le_max_left ..) (le_max_right ..)
          hlead _ hout
    · exact Prod.ext rfl (Prod.ext (zero_add _).symm hz)

end SympyProofs.Calculus.Antiderivative.Solve
