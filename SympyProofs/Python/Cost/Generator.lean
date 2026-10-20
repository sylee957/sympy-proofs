module

public import SympyProofs.Python.Cost
public import SympyProofs.Python.Generator.Correctness

/-!
# Lazy delivery of generator costs

The ordinary interpreter ignores events. The instrumented interpreter yields
either an event or a user value. A consuming loop forwards events to its own
`MonadCost`; stopping that loop never executes the remaining continuation.
This avoids charging a generator eagerly or losing its final search on exhaustion.
-/

@[expose] public section

universe v

namespace Python.Cost

instance (priority := low) {V : Type} : MonadCost (Generator.Computation V) where
  emit _ := pure ()

/-- Interpret generator effects as lazy stream entries. -/
@[instance_reducible] def eventCost {V : Type} : MonadCost (Generator.Computation (Event ⊕ V)) where
  emit event := Generator.yield (.inl event)

/-- A lazy stream with interleaved, unconsumed cost events. -/
structure Stream (V : Type) where
  computation : Generator.Computation (Event ⊕ V) Unit

instance {V : Type} {m : Type → Type v} [Monad m] [MonadCost m] :
    ForIn m (Stream V) V where
  forIn stream state body := ForIn.forIn stream.computation state fun entry state => do
    match entry with
    | .inl event =>
        MonadCost.emit event
        return .yield state
    | .inr value => body value state

end Python.Cost
