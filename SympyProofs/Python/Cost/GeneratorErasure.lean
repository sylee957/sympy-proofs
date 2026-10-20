module

public import SympyProofs.Python.Cost.Erasure
public import SympyProofs.Python.Cost.Generator
public import SympyProofs.Python.Generator.Execution

/-! # Erasing lazy generator cost events

The trace relation records actual suspension/resumption steps. Its consumer
rule preserves yielded values, their order, and early exit while ignoring cost.
-/

@[expose] public section

open Generator
namespace Python.Cost
/-- Remove cost entries without changing the order of yielded values. -/
def values {V : Type} (xs : List (Event ⊕ V)) : List V :=
  xs.filterMap (fun e => match e with | .inl _ => none | .inr v => some v)
/-- An actual finite execution, with events hidden from its user-visible trace. -/
def Yields {V α : Type} (c : Computation (Event ⊕ V) α) (a : α) (vs : List V) : Prop :=
  ∃ xs, Returns c a xs ∧ values xs = vs
namespace Yields
variable {V α β : Type}
theorem pure (a : α) : Yields (Pure.pure a) a ([] : List V) := ⟨[], .done a, rfl⟩
theorem perform (event : Event) (a : α) :
    Yields (V := V) (letI := eventCost (V := V); Python.Cost.perform event a) a [] := by
  exact ⟨[.inl event], (Returns.yield_one _).bind (.done a), rfl⟩
theorem emit (event : Event) :
    Yields (V := V) (letI := eventCost (V := V); MonadCost.emit event) () [] := by
  exact ⟨[.inl event], Returns.yield_one _, rfl⟩
theorem yield (v : V) : Yields (Generator.yield (.inr v)) () [v] :=
  ⟨[.inr v], Returns.yield_one _, rfl⟩
theorem bind {c : Computation (Event ⊕ V) α} {f : α → Computation (Event ⊕ V) β}
    {a b xs ys} (h : Yields c a xs) (hf : Yields (f a) b ys) :
    Yields (c >>= f) b (xs++ys) := by
  obtain ⟨as,ha,hva⟩ := h
  obtain ⟨bs,hb,hvb⟩ := hf
  exact ⟨as++bs,ha.bind hb,by simp only [values,List.filterMap_append] at *; rw [hva,hvb]⟩
theorem skip {c next : Computation (Event ⊕ V) α} {a xs}
    (h : c.step = .skip next) (hn : Yields next a xs) : Yields c a xs := by
  obtain ⟨es,hr,he⟩ := hn
  exact ⟨es,.skip h hr,he⟩
end Yields
namespace Erases
variable {V σ : Type}
theorem forIn_events (xs : List (Event ⊕ V))
    (body : V → σ → CostT Id (ForInStep σ)) (f : V → σ → ForInStep σ)
    (hbody : ∀ v ∈ values xs, ∀ s, Erases (body v s) (f v s)) (s : σ) :
    Erases (ForIn.forIn xs s (fun e s => match e with
      | .inl event => do MonadCost.emit event; Pure.pure (.yield s)
      | .inr v => body v s))
      (Id.run (ForIn.forIn (values xs) s (fun v s => Pure.pure (f v s)))) := by
  induction xs generalizing s with
  | nil => exact pure s
  | cons e xs ih =>
    cases e with
    | inl event =>
      simp only [List.forIn_cons, values, List.filterMap_cons, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
      apply (emit event).bind
      exact ih hbody s
    | inr v =>
      simp only [values, List.filterMap_cons, List.forIn_cons]
      apply (hbody v (by simp [values]) s).bind
      cases h : f v s with
      | done t => exact pure t
      | yield t => exact ih (fun w hw s => hbody w (by simp [values] at hw ⊢; exact Or.inr hw) s) t
end Erases

/-- Hiding event entries preserves every consumer, including an early exit. -/
theorem Yields.forIn_erases {V α σ : Type} {c : Computation (Event ⊕ V) α} {a vs}
    (h : Yields c a vs) (body : V → σ → CostT Id (ForInStep σ))
    (f : V → σ → ForInStep σ)
    (hbody : ∀ v ∈ vs, ∀ s, Erases (body v s) (f v s)) (s : σ) :
    Erases (ForIn.forIn c s (fun e s => match e with
      | .inl event => do MonadCost.emit event; Pure.pure (.yield s)
      | .inr v => body v s))
      (Id.run (ForIn.forIn vs s (fun v s => Pure.pure (f v s)))) := by
  obtain ⟨xs,hr,he⟩ := h
  rw [hr.produces.forIn]
  subst vs
  exact Erases.forIn_events xs body f hbody s
end Python.Cost
