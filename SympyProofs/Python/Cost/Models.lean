module

public import SympyProofs.Python.Cost
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Selectable cost models

Unit counts, per-operation counts, byte visits, and produced payload can all be
read from the same trace. `schoolbook` is an explicit reference charging policy
for bit arithmetic and linear buffer work; it is not a proved bound on CPython.
In particular Python may use faster multiplication, cached objects and optimized
byte scans. Proving an implementation realizes a policy is a separate obligation.

Buffer payload totals measure cumulative production, not peak space. Integer
result widths measure value sizes, not Python object sizes or allocation counts.
-/

@[expose] public section

namespace Python.Cost.Models

def operations : Model := fun _ => 1

def integerCalls (op : IntOp) : Model
  | .integer e => if e.op = op then 1 else 0
  | _ => 0

def bufferCalls (kind : BufferKind) (op : BufferOp) : Model
  | .buffer e => if e.kind = kind ∧ e.op = op then 1 else 0
  | _ => 0

def byteReads : Model
  | .buffer e => e.read
  | _ => 0

def byteWrites : Model
  | .buffer e => e.written
  | _ => 0

def createdBytes : Model
  | .buffer e => e.created
  | _ => 0

def resultBits : Model
  | .integer e => e.result.natAbs.size
  | _ => 0

/-- Cumulative reference slots created by list operations, separately from byte payload. -/
def createdSlots : Model
  | .sequence _ _ created => created
  | _ => 0

/-- At least one bit of work is charged even for a zero-valued operand. -/
def width (x : ℤ) : ℕ := max 1 x.natAbs.size

/-- Quadratic multiplication/long division and binary exponentiation reference charges.
Exponentiation uses the exponent's *bit length* and the maximum operand/result
width; shifts include output width and inspection of the shift count. -/
def integerSchoolbook (e : IntegerEvent) : ℕ :=
  let a := width (e.args[0]?.getD 0)
  let b := width (e.args[1]?.getD 0)
  let r := width e.result
  match e.op with
  | .mul => a * b + r
  | .floorDiv | .mod => a * b + a + b + r
  | .pow =>
      let extent := max a r
      (2 * b + 1) * extent * extent
  | .shiftLeft | .shiftRight => a + b + r
  | .add | .sub | .bitAnd => max a b + r
  | .neg | .bitCount | .bitLength => a + r
  | .eq | .lt => max a b
  | .truth => 1
  | .isqrt => a * a + r

/-- One dispatch unit, sequential buffer visits and logical payload production.
This deliberately charges materialization even if a particular runtime reuses it. -/
def schoolbook : Model
  | .integer e => 1 + integerSchoolbook e
  | .buffer e => 1 + e.read + e.written + e.created +
      (e.args.map width).sum
  | .sequence _ visited created => 1 + visited + created
  | .control _ => 1

@[simp] theorem charge_operations (events : List Event) :
    charge operations events = events.length := by
  induction events with
  | nil => rfl
  | cons e es ih => simp [charge, operations] at ih ⊢; omega

/-- Models may be added to measure several kinds of work together. -/
theorem charge_add (f g : Model) (events : List Event) :
    charge (fun e => f e + g e) events = charge f events + charge g events := by
  induction events with
  | nil => rfl
  | cons e es ih => simp only [charge, List.map_cons, List.sum_cons] at ih ⊢; omega

end Python.Cost.Models
