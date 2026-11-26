module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Columns

/-! The starting columns represent arbitrary parameters, a zero partial solution and the
associated linear combination of input polynomials. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

private theorem initial_length (ps : List (Poly (K R n))) : (initial ps).length = ps.length := by
  simp [initial]

private theorem vector_unit {F : Type} [Field F] (f : F →+* k) {m : ℕ} (i : Fin m) :
    Linear.vector f m (Linear.unit m i) = Pi.single i 1 := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [Linear.vector, Linear.unit, List.getD_eq_getElem?_getD, i.isLt]
  · have hn : j.val ≠ i.val := fun e => h (Fin.ext e)
    simp [Linear.vector, Linear.unit, List.getD_eq_getElem?_getD, j.isLt, h, hn]

private theorem initial_get (ps : List (Poly (K R n))) (j : Fin (initial ps).length) :
    (initial ps).get j = ⟨Linear.unit ps.length j, 0, ps.get (Fin.cast (initial_length ps) j)⟩ := by
  simp [initial, List.get_eq_getElem, List.getElem_zipIdx]

private theorem initial_accumulate (ps : List (Poly (K R n))) (u : Fin ps.length → k) :
    Linear.accumulate (initial ps) (Column.value k ps.length)
        (fun i => u (Fin.cast (initial_length ps) i)) =
          (u,0,Linear.accumulate ps (modelPoly k) u) := by
  classical
  rw [Linear.accumulate_apply]
  have he := Fintype.sum_equiv (finCongr (initial_length ps))
    (fun i => u (Fin.cast (initial_length ps) i) • Column.value k ps.length ((initial ps).get i))
    (fun j => u j • (Pi.single j 1, (0 : Polynomial (M k n)), modelPoly k (ps.get j)))
    (fun i => by
      rw [initial_get]
      change _ • (Linear.vector (Model.constantHom k) _
        (Linear.unit _ (Fin.cast (initial_length ps) i).val), _, _) = _
      rw [vector_unit]
      simp [modelPoly])
  rw [he]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [Prod.snd_sum, Prod.fst_sum]
  · simp [Prod.snd_sum, Linear.accumulate_apply]

/-- Characterization of all parameter directions before any equations have been imposed. -/
theorem mem_initial_iff (ps : List (Poly (K R n)))
    (z : (Fin ps.length → k) × Polynomial (M k n) × Polynomial (M k n)) :
    z ∈ Submodule.span k (Column.value k ps.length '' {v | v ∈ initial ps}) ↔
      z.2.1 = 0 ∧ z.2.2 = Linear.accumulate ps (modelPoly k) z.1 := by
  rw [Linear.mem_columns_iff]
  constructor
  · rintro ⟨v,rfl⟩
    let u := fun j => v (Fin.cast (initial_length ps).symm j)
    have he : v = fun i => u (Fin.cast (initial_length ps) i) := by ext i; rfl
    rw [he, initial_accumulate]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hsol,hr⟩
    exact ⟨_, (initial_accumulate k ps z.1).trans (Prod.ext rfl (Prod.ext hsol.symm hr.symm))⟩

end SympyProofs.Calculus.Antiderivative.Solve
