module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Operator

/-! Simultaneous coefficient solving preserves every parameter direction and every choice
of the new polynomial coefficient satisfying its equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

private theorem parameter_kernel_width {t : Tower R n} {lower : Level R n}
    (hl : lower.SolveSpec k t) (f : K R n) (gs : List (K R n)) (m : ℕ)
    (hm : m = gs.length) (a : Fin m → k) (y : M k n) :
    let (hs, rows) := lower.solve f gs
    (a,y) ∈ Submodule.span k
        ((fun q : List (K R 0) => (Linear.vector (Model.constantHom k) m q,
          val k (Level.combine (q.drop m) hs))) '' {q | q ∈ Linear.kernel rows (m + hs.length)}) ↔
      t.modelD k y + val k f * y = Model.linearCombination k (List.ofFn a) gs := by
  subst m
  exact parameter_kernel_spec k hl _ _ _ _

/-- The span of an extended family consists of exactly the old coordinate combinations and
new coefficients that satisfy the lower-field equation. -/
theorem mem_extendSolutions_iff {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (g : ReducedGen (K R n)) (a b : Poly (K R n)) (w i : ℕ) (vs : List (Column R n))
    (f : K R n) (gs : List (K R n)) (hlen : gs.length = vs.length) (y : State k n w) :
    y ∈ Submodule.span k (Column.value k w '' {c |
        c ∈ extendSolutions t.D (g.velocity t.D) a b lower w i vs f gs}) ↔
      ∃ (params : Fin vs.length → k) (c : M k n),
        t.modelD k c + val k f * c = Model.linearCombination k (List.ofFn params) gs ∧
        extendMap k w i (operator k t g a b)
          (Linear.accumulate vs (Column.value k w) params, c) = y := by
  obtain ⟨hs,rows,hdata⟩ : ∃ hs rows, lower.solve f gs = (hs,rows) := ⟨_,_,rfl⟩
  let u (q : List (K R 0)) := (Linear.vector (Model.constantHom k) vs.length q,
    val k (Level.combine (q.drop vs.length) hs))
  let T := (extendMap k w i (operator k t g a b)).comp
    ((Linear.accumulate vs (Column.value k w)).prodMap (LinearMap.id (R := k) (M := M k n)))
  have hT (q : List (K R 0)) :
      (extend t.D (g.velocity t.D) a b i (combine w vs q)
        (Level.combine (q.drop vs.length) hs)).value k w = T (u q) := by
    rw [value_extend, value_combine]
    rfl
  rw [extendSolutions, hdata]
  rw [Linear.mem_mapped_columns_iff _ u _ _ T (fun q _ => hT q)]
  have hp (v : Fin vs.length → k) (c : M k n) := parameter_kernel_width k hl f gs
    vs.length hlen.symm v c
  simp only [hdata] at hp
  constructor
  · rintro ⟨⟨params,c⟩,h,hy⟩
    exact ⟨params,c,(hp params c).mp h,hy⟩
  · rintro ⟨params,c,h,hy⟩
    exact ⟨(params,c),(hp params c).mpr h,hy⟩

end SympyProofs.Calculus.Antiderivative.Solve
