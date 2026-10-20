module

public import SympyProofs.Python.Cost.Instrumentation.Program
public import Init.Data.List.Monadic

/-! Finite-loop contracts for automatically translated imperative bodies.
Each visited element emits `for.next`; an early `break` skips the remaining
elements. List construction and the loop body's operations are charged separately.
-/

@[expose] public section
namespace Python.Cost.Instrumentation.Checked
variable {α β : Type}

def stepYield (b : β) : Checked (ForInStep.yield b) := pure _
def stepDone (b : β) : Checked (ForInStep.done b) := pure _

def listForIn (xs : List α) (initial : β) (f : α → β → Id (ForInStep β))
    (step : ∀ a b, Checked (f a b)) :
    Checked (ForIn.forIn xs initial f) :=
  match xs with
  | [] => pure initial
  | x :: xs =>
    let body :=
      bind (f := fun _ : Unit =>
        match f x initial with
        | .done b => b
        | .yield b => ForIn.forIn xs b f)
        (primitive (.control "for.next") ()) fun _ =>
      bind (f := fun s : ForInStep β =>
        match s with
        | .done b => b
        | .yield b => ForIn.forIn xs b f)
        (step x initial) fun s =>
          match s with
          | .done b => pure b
          | .yield b => listForIn xs b f step
    ⟨body.program, by
      rw [body.correct, List.forIn_cons]
      rfl⟩

end Python.Cost.Instrumentation.Checked
