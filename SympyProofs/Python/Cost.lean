module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Size

/-!
# Effects for Python operation costs

The same program can run in `Id` (values only), `TraceT` (operation events), or
`CostT` (a running charge under a supplied model). These are monad transformers:
costs belong to execution, never to a `PythonInt` value or its ring equality.

Events observe operands and buffer sizes. Computing this metadata in Lean is
instrumentation, not an extra operation in the modeled Python program. A model
is a charging policy, not automatically a theorem about CPython wall-clock time.
Only explicitly instrumented operations are charged; bind, casts, literals,
control flow, generator suspension, and garbage collection are not implicit events.
-/

@[expose] public section

universe v

namespace Python.Cost

inductive IntOp where
  | add | sub | neg | mul | floorDiv | mod | pow
  | bitAnd | shiftLeft | shiftRight | bitCount | bitLength
  | eq | lt | truth | isqrt
  deriving DecidableEq, Repr

inductive BufferKind where
  | bytes | bytearray
  deriving DecidableEq, Repr

inductive BufferOp where
  | literal | ofBytes | len | get | repeat | set | setSlice | find
  deriving DecidableEq, Repr

/-- Integer operands and result, observed through the value model. -/
structure IntegerEvent where
  op : IntOp
  args : List ℤ
  result : ℤ
  deriving DecidableEq, Repr

/-- Logical buffer work. `read` uses a sequential scan model; `created` is the
payload length of a newly produced buffer, not actual allocation or peak memory.
Mutation records selected writes without assuming a copy of the whole carrier. -/
structure BufferEvent where
  kind : BufferKind
  op : BufferOp
  args : List ℤ := []
  before : ℕ := 0
  after : ℕ := 0
  read : ℕ := 0
  written : ℕ := 0
  created : ℕ := 0
  deriving DecidableEq, Repr

inductive Event where
  | integer (data : IntegerEvent)
  | buffer (data : BufferEvent)
  /-- Sequence administration: operation name, elements visited, new reference slots.
  Append uses an amortized mutable-list policy, not Lean's persistent allocation. -/
  | sequence (op : String) (visited created : ℕ)
  /-- One abstract control step: call, iteration, yield, or resume. -/
  | control (op : String)
  deriving DecidableEq, Repr

/-- A chosen nonnegative charge for each primitive event. -/
abbrev Model := Event → ℕ

class MonadCost (m : Type → Type v) where
  emit : Event → m Unit

instance : MonadCost Id := ⟨fun _ => ()⟩

/-- Execute a value-producing primitive and record exactly one event. -/
def perform {m : Type → Type v} [Monad m] [MonadCost m] {α : Type}
    (event : Event) (value : α) : m α := do
  MonadCost.emit event
  return value

/-- A reader chooses the model; the state accumulates its charges. -/
abbrev CostT (m : Type → Type v) := ReaderT Model (StateT ℕ m)

instance {m : Type → Type v} [Monad m] : MonadCost (CostT m) where
  emit event := fun model total => pure ((), total + model event)

namespace CostT

def run {m : Type → Type v} {α : Type} (program : CostT m α)
    (model : Model) (initial : ℕ := 0) : m (α × ℕ) := program model initial

@[simp] theorem run_pure {α : Type} (value : α) (model : Model) (initial : ℕ) :
    run (pure value : CostT Id α) model initial = (value, initial) := rfl

@[simp] theorem run_perform {α : Type} (event : Event) (value : α)
    (model : Model) (initial : ℕ) :
    run (perform event value : CostT Id α) model initial =
      (value, initial + model event) := rfl

/-- Charges compose in execution order, including operations whose result is discarded. -/
theorem run_bind {α β : Type} (program : CostT Id α) (next : α → CostT Id β)
    (model : Model) (initial : ℕ) :
    run (program >>= next) model initial =
      let (value, total) := run program model initial
      run (next value) model total := rfl

end CostT

/-- Reverse event list gives constant-time insertion; `run` restores execution order. -/
abbrev TraceT (m : Type → Type v) := StateT (List Event) m

instance {m : Type → Type v} [Monad m] : MonadCost (TraceT m) where
  emit event := fun events => pure ((), event :: events)

namespace TraceT

def run {m : Type → Type v} [Functor m] {α : Type} (program : TraceT m α) :
    m (α × List Event) := (fun (value, events) => (value, events.reverse)) <$> program []

@[simp] theorem run_perform {α : Type} (event : Event) (value : α) :
    run (perform event value : TraceT Id α) = (value, [event]) := rfl

end TraceT

/-- Re-price a recorded execution without running the algorithm again. -/
def charge (model : Model) (events : List Event) : ℕ := (events.map model).sum

@[simp] theorem charge_append (model : Model) (xs ys : List Event) :
    charge model (xs ++ ys) = charge model xs + charge model ys := by
  simp [charge]

/-- Incremental accumulation and summing the trace assign identical costs. -/
theorem foldl_charge (model : Model) (events : List Event) (initial : ℕ) :
    events.foldl (fun total event => total + model event) initial =
      initial + charge model events := by
  induction events generalizing initial with
  | nil => simp [charge]
  | cons event events ih => simp [List.foldl, ih, charge, Nat.add_assoc]

end Python.Cost
