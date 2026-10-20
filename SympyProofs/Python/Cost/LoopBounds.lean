module

public import SympyProofs.Python.Cost.Bounds
public import Init.Internal.Order.While

/-! # Compositional cost bounds for terminating imperative loops -/

@[expose] public section
open Python.Cost
namespace Python.Cost.Bounded
variable {σ : Type} {model : Model}
/-- A decreasing natural measure pays for every iteration and the final exit test. -/
theorem loop (body : σ → CostT Id (ForInStep σ)) (inv post : σ → Prop)
    (rank : σ → ℕ) (stepCost : ℕ)
    (hbody : ∀ s, inv s → Bounded model (body s)
      (fun r => match r with
        | .done t => post t
        | .yield t => inv t ∧ rank t < rank s) stepCost)
    (s : σ) (hs : inv s) :
    Bounded model (Lean.Loop.forIn ⟨⟩ s (fun _ => body)) post ((rank s + 1) * stepCost) := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  have h := (hbody s hs).bind (post' := post)
    (d := rank s * stepCost) (next := fun r => match r with
      | .done t => Pure.pure t
      | .yield t => Lean.Loop.forIn ⟨⟩ t (fun _ => body)) (by
        intro r hr
        cases r with
        | done t => exact (Bounded.pure t hr).mono (fun _ h => h) (Nat.zero_le _)
        | yield t =>
          exact (loop body inv post rank stepCost hbody t hr.1).mono (fun _ h => h)
            (Nat.mul_le_mul_right stepCost (by omega)))
  exact h.mono (fun _ h => h) (by rw [Nat.add_mul]; omega)
termination_by rank s
end Python.Cost.Bounded
