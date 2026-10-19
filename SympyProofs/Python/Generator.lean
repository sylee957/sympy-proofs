module

public import Std.Data.Iterators

/-!
# Resumable generators in ordinary `do` notation

`Generator.yield` suspends a computation. Monadic bind saves the rest of the
body as a continuation. The `ForIn` instance for `Lean.Loop` represents standard
`while`/`repeat` loops explicitly, so even an infinite generator has a finite
representation. `create` defers initialization until iteration begins.

The interpreter takes small steps: internal steps yield no value, and a yield
stores its continuation without executing it. It retains no running call stack
between yields. This is a value model of `next`/`yield`, not Python object
aliasing, `send`, `throw`, `close`, or exceptions.
-/

@[expose] public section

namespace Generator

/-- A generator body returning `α` and emitting values of type `Value`. -/
inductive Computation (Value : Type) : Type → Type 1 where
  | done {α} (result : α) : Computation Value α
  | suspended {α} (value : Value) (resume : Unit → Computation Value α) : Computation Value α
  | deferred {α} (resume : Unit → Computation Value α) : Computation Value α
  | loop {α} (State : Type) (body : State → Computation Value (ForInStep State))
      (state : State) (after : State → Computation Value α) : Computation Value α

/-- Append a continuation, saving it across yields and loop iterations. -/
def bind {V α β : Type} : Computation V α → (α → Computation V β) → Computation V β
  | .done a, f => f a
  | .suspended v k, f => .suspended v (fun () => bind (k ()) f)
  | .deferred k, f => .deferred (fun () => bind (k ()) f)
  | .loop S body s after, f => .loop S body s (fun s => bind (after s) f)

instance {V : Type} : Monad (Computation V) where
  pure := .done
  bind := bind

/-- Emit one value; the following statement runs only after resumption. -/
def yield {V : Type} (value : V) : Computation V Unit :=
  .suspended value (fun () => .done ())

/-- Construct a generator without executing its body. -/
def create {V α : Type} (body : Unit → Computation V α) : Computation V α := .deferred body

/-- Standard Lean `while` and `repeat` syntax saves its loop state here. -/
instance {V : Type} : ForIn (Computation V) Lean.Loop Unit where
  forIn _ state body := .loop _ (body ()) state .done

/-- One interpreter transition. A yielded continuation stays deferred. -/
def Computation.step {V α : Type} :
    Computation V α → Std.IterStep (Computation V α) (ULift.{1} V)
  | .done _ => .done
  | .suspended value resume => .yield (.deferred resume) ⟨value⟩
  | .deferred resume => .skip (resume ())
  | .loop S body state after => .skip (bind (body state) fun
      | .done state => after state
      | .yield state => .loop S body state after)

/-- States reachable by interpreter steps, including internal steps. -/
inductive Reachable {V α : Type} (initial : Computation V α) : Computation V α → Prop
  | refl : Reachable initial initial
  | next {current next} : Reachable initial current →
      current.step.successor = some next → Reachable initial next

/-- A saved continuation together with its reachability invariant. -/
abbrev Frame {V α : Type} (initial : Computation V α) :=
  { current : Computation V α // Reachable initial current }

/-- Adapt an interpreter step to a frame; proofs have no runtime cost. -/
def Frame.step {V α : Type} {initial : Computation V α} (frame : Frame initial) :
    Std.IterStep (Frame initial) (ULift.{1} V) :=
  match h : frame.val.step with
  | .done => .done
  | .yield next value => .yield ⟨next, .next frame.property (by simp [h])⟩ value
  | .skip next => .skip ⟨next, .next frame.property (by simp [h])⟩

instance {V α : Type} {initial : Computation V α} :
    Std.Iterator (Frame initial) Id (ULift.{1} V) where
  IsPlausibleStep it step := step = it.internalState.step.mapIterator (fun frame => ⟨frame⟩)
  step it := pure (.deflate ⟨it.internalState.step.mapIterator (fun frame => ⟨frame⟩), rfl⟩)

instance {V α : Type} {initial : Computation V α} {m : Type w → Type w'} [Monad m] :
    Std.IteratorLoop (Frame initial) Id m := .defaultImplementation

/-- Begin at the initial continuation. `ULift` only bridges the iterator's universes. -/
def Computation.iter {V α : Type} (initial : Computation V α) :
    Std.Iter (α := Frame initial) (ULift.{1} V) := ⟨⟨initial, .refl⟩⟩

/-- Consume yields directly, allowing the consumer to stop without resuming again. -/
instance {V α : Type} {m : Type → Type v} [Monad m] : ForIn m (Computation V α) V where
  forIn initial state body := ForIn.forIn initial.iter state (fun value s => body value.down s)

/-- Collect the yields. Infinite generators may diverge; finiteness is proved separately. -/
def Computation.toList {V α : Type} (initial : Computation V α) : List V :=
  initial.iter.toList.map ULift.down

/-- Resume until a yield or normal return. Productivity rules out endless internal steps. -/
def next {V α : Type} {initial : Computation V α} [Std.Iterators.Productive (Frame initial) Id]
    (it : Std.Iter (α := Frame initial) (ULift.{1} V)) :
    Option V × Std.Iter (α := Frame initial) (ULift.{1} V) :=
  match it.step with
  | ⟨.done, _⟩ => (none, it)
  | ⟨.yield it' value, _⟩ => (some value.down, it')
  | ⟨.skip it', _h⟩ => next it'
termination_by it.finitelyManySkips

end Generator
