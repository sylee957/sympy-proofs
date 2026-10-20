module

public import SympyProofs.Python.Cost.Bounds

/-!
# Certified generated instrumentation

`Program` is the internal output of instrumentation, not a source language the
algorithm author writes. A primitive records one specified event. `bind` evaluates
its first argument once and passes the resulting value to its continuation.
The finite operational semantics proves both the returned value and the exact
trace, and connects that trace to every `CostT` charging policy.

These are costs of the declared operation model, not Lean compiler or CPython
machine costs. The elaborator's supported-operation audit is a separate check;
value equality alone cannot detect a missing operation event.
-/

@[expose] public section
universe v

namespace Python.Cost.Instrumentation

inductive Program : Type → Type 1 where
  | pure {α : Type} (value : α) : Program α
  | primitive {α : Type} (event : Event) (value : α) : Program α
  | bind {α β : Type} (first : Program α) (next : α → Program β) : Program β

namespace Program

variable {α β : Type}

/-- Interpret the generated program using the existing cost interface. -/
def run {m : Type → Type v} [Monad m] [MonadCost m] : {α : Type} → Program α → m α
  | _, .pure a => Pure.pure a
  | _, .primitive event a => perform event a
  | _, .bind p f => do
    let a ← run p
    run (f a)

/-- Value semantics of the same generated program. -/
def value : {α : Type} → Program α → α
  | _, .pure a => a
  | _, .primitive _ a => a
  | _, .bind p f => value (f (value p))

def events : {α : Type} → Program α → List Event
  | _, .pure _ => []
  | _, .primitive event _ => [event]
  | _, .bind p f => events p ++ events (f (value p))

/-- Finite execution records every primitive, in execution order. -/
inductive Executes : {α : Type} → Program α → α → List Event → Prop
  | pure {α : Type} (a : α) : Executes (.pure a) a []
  | primitive {α : Type} (event : Event) (a : α) : Executes (.primitive event a) a [event]
  | bind {α β : Type} {p : Program β} {f : β → Program α} {a b xs ys} :
      Executes p a xs → Executes (f a) b ys → Executes (.bind p f) b (xs ++ ys)

theorem executes (p : Program α) : Executes p p.value p.events := by
  induction p with
  | pure a => exact .pure a
  | primitive event a => exact .primitive event a
  | bind p f ih ihf => exact .bind ih (ihf _)

/-- The operational semantics determines both the result and the whole trace. -/
theorem Executes.deterministic {p : Program α} {a : α} {es : List Event}
    (h : Executes p a es) : a = p.value ∧ es = p.events := by
  induction h with
  | pure => exact ⟨rfl, rfl⟩
  | primitive => exact ⟨rfl, rfl⟩
  | bind hp hf ih ihf =>
    rcases ih with ⟨rfl, rfl⟩
    rcases ihf with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem run_id (p : Program α) : Id.run (p.run (m := Id)) = p.value := by
  induction p with
  | pure => rfl
  | primitive => rfl
  | bind p f ih ihf =>
    change Id.run ((f (Id.run (p.run (m := Id)))).run (m := Id)) = _
    rw [ih]
    exact ihf _

/-- Recording preserves any already recorded prefix without repeating it. -/
theorem run_trace (p : Program α) (prior : List Event) :
    p.run (m := TraceT Id) prior = (p.value, p.events.reverse ++ prior) := by
  induction p generalizing prior with
  | pure => rfl
  | primitive => rfl
  | bind p f ih ihf =>
    change (let (a, es) := p.run (m := TraceT Id) prior;
      (f a).run (m := TraceT Id) es) = _
    rw [ih]
    dsimp only
    rw [ihf]
    simp [events, value, List.reverse_append, List.append_assoc]

/-- Every charge is justified by a primitive in the operational trace. -/
theorem run_cost (p : Program α) (model : Model) (initial : ℕ) :
    CostT.run (p.run (m := CostT Id)) model initial =
      (p.value, initial + charge model p.events) := by
  induction p generalizing initial with
  | pure => rfl
  | primitive event a => simp [run, value, events, charge]
  | bind p f ih ihf =>
    rw [run, CostT.run_bind, ih]
    dsimp only
    rw [ihf]
    simp [value, events, Nat.add_assoc]

theorem trace_run (p : Program α) :
    TraceT.run (p.run (m := TraceT Id)) = (p.value, p.events) := by
  change ((p.run (m := TraceT Id) []).1, (p.run (m := TraceT Id) []).2.reverse) = _
  simp [run_trace]

end Program

/-- A generated program accompanied by a kernel-checked value-preservation proof. -/
structure Checked {α : Type} (source : α) where
  program : Program α
  correct : program.value = source

namespace Checked
variable {α β : Type}

def pure (a : α) : Checked a := ⟨.pure a, rfl⟩
def primitive (event : Event) (a : α) : Checked a := ⟨.primitive event a, rfl⟩

/-- Identify the standard `Id` return instance when auditing a source wrapper. -/
def idPure (a : α) : Checked (Pure.pure a : Id α) := pure _

/-- Identify the standard `Id` bind instance. The translator instruments both
arguments separately; this certificate is used only to check the wrapper. -/
def idBind (a : Id α) (f : α → Id β) : Checked (Bind.bind a f : Id β) := pure _

def bind {a : α} {f : α → β} (p : Checked a) (next : ∀ x, Checked (f x)) :
    Checked (f a) :=
  ⟨.bind p.program (fun x => (next x).program), by
    change (next p.program.value).program.value = _
    rw [(next _).correct, p.correct]⟩

def run {a : α} (p : Checked a) {m : Type → Type v} [Monad m] [MonadCost m] : m α :=
  p.program.run

theorem run_id {a : α} (p : Checked a) : Id.run (p.run (m := Id)) = a := by
  rw [run, Program.run_id, p.correct]

theorem run_cost {a : α} (p : Checked a) (model : Model) (initial : ℕ) :
    CostT.run (p.run (m := CostT Id)) model initial =
      (a, initial + charge model p.program.events) := by
  rw [run, Program.run_cost, p.correct]

theorem run_trace {a : α} (p : Checked a) :
    TraceT.run (p.run (m := TraceT Id)) = (a, p.program.events) := by
  rw [run, Program.trace_run, p.correct]

/-- Independent interpreters agree on both the value and the charge of the trace. -/
theorem cost_eq_trace {a : α} (p : Checked a) (model : Model) (initial : ℕ) :
    CostT.run (p.run (m := CostT Id)) model initial =
      (a, initial + charge model (TraceT.run (p.run (m := TraceT Id))).2) := by
  rw [p.run_trace, p.run_cost]

/-- Branches are selected after the condition; only the selected program runs. -/
def branch {b : Bool} {x y : α} (test : Checked b)
    (yes : Unit → Checked x) (no : Unit → Checked y) : Checked (if b then x else y) :=
  bind (f := fun c : Bool => if c then x else y) test fun c => by
    cases c
    · exact no ()
    · exact yes ()

/-- A proposition-based Lean `if` uses the same recorded Boolean decision. -/
def branchProp (p : Prop) [Decidable p] {x y : α} (test : Checked (decide p))
    (yes : Unit → Checked x) (no : Unit → Checked y) : Checked (if p then x else y) :=
  ⟨(branch test yes no).program, by
    rw [(branch test yes no).correct]
    by_cases h : p <;> simp [h]⟩

end Checked
end Python.Cost.Instrumentation
