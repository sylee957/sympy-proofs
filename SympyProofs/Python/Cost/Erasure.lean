module

public import SympyProofs.Python.Cost.Bounds
public import Init.Internal.Order.While

/-! # Value preservation by cost instrumentation

`Erases` compares executable code for every charging policy and initial counter.
Its compositional rules preserve values, branches, and loop transitions; no
mathematical specification of an algorithm is used.
-/

@[expose] public section

namespace Python.Cost

/-- The cost interpreter preserves this value for every policy and initial counter. -/
def Erases {α : Type} (program : CostT Id α) (value : α) : Prop :=
  ∀ model initial, (CostT.run program model initial).1 = value

namespace Erases

variable {α β σ τ : Type}

theorem pure (a : α) : Erases (pure a) a := by intro model initial; rfl

theorem perform (event : Event) (a : α) : Erases (perform event a) a := by intro model initial; rfl

theorem emit (event : Event) : Erases (MonadCost.emit event) () := by intro model initial; rfl

theorem bind {p : CostT Id α} {f : α → CostT Id β} {a : α} {b : β}
    (hp : Erases p a) (hf : Erases (f a) b) : Erases (p >>= f) b := by
  intro model initial
  rw [CostT.run_bind]
  change (CostT.run (f (CostT.run p model initial).1) model
    (CostT.run p model initial).2).1 = b
  rw [hp model initial]
  exact hf _ _

theorem foldlM (xs : List α) (step : σ → α → CostT Id σ) (f : σ → α → σ)
    (hstep : ∀ s x, x ∈ xs → Erases (step s x) (f s x)) (s : σ) :
    Erases (xs.foldlM step s) (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact pure s
  | cons x xs ih =>
    exact (hstep s x (by simp)).bind (ih (fun s y hy => hstep s y (by simp [hy])) _)

theorem forIn_list (xs : List α) (step : α → σ → CostT Id (ForInStep σ))
    (f : α → σ → ForInStep σ)
    (hstep : ∀ x ∈ xs, ∀ s, Erases (step x s) (f x s)) (s : σ) :
    Erases (ForIn.forIn xs s step) (Id.run (ForIn.forIn xs s (fun x s => Pure.pure (f x s)))) := by
  induction xs generalizing s with
  | nil => exact pure s
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply (hstep x (by simp) s).bind
    cases h : f x s with
    | done t => exact pure t
    | yield t => exact ih (fun y hy s => hstep y (by simp [hy]) s) t

/-- Match each loop transition, using the pure state as its termination measure. -/
theorem loop (body : τ → CostT Id (ForInStep τ)) (step : σ → ForInStep σ)
    (embed : σ → τ) (inv : σ → Prop) (rank : σ → ℕ)
    (hbody : ∀ s, inv s → Erases (body (embed s))
      (match step s with | .done t => .done (embed t) | .yield t => .yield (embed t)))
    (hnext : ∀ s t, inv s → step s = .yield t → inv t ∧ rank t < rank s)
    (s : σ) (hs : inv s) :
    Erases (Lean.Loop.forIn ⟨⟩ (embed s) (fun _ => body))
      (embed (Id.run (Lean.Loop.forIn ⟨⟩ s (fun _ s => Pure.pure (step s))))) := by
  rw [Lean.Loop.forIn_eq_of_monadTail, Lean.Loop.forIn_eq_of_monadTail]
  apply (hbody s hs).bind
  cases h : step s with
  | done t => exact pure (embed t)
  | yield t =>
    exact loop body step embed inv rank hbody hnext t (hnext s t hs h).1
termination_by rank s
decreasing_by exact (hnext s t hs h).2

end Erases
end Python.Cost
