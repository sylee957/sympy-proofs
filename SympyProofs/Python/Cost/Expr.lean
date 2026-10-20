module

public import SympyProofs.Python.Cost.Int

/-!
# Integer computations with ordinary arithmetic notation

`CostExpr m I` wraps an `m I` computation. Its operation instances evaluate their
operands from left to right and then execute one instrumented Python operation.
There is no custom parser, and the wrapper does not claim ring laws: rewriting
an expression algebraically can change both its effects and its cost.

`value` explicitly lifts an already computed integer without charging it. There
are no coercions from integers: an implicit cast of an already evaluated
expression could silently omit its operations. Numerals lift literal values.
`run` executes an
expression. For a universe-preserving monad, `eval` also wraps the resulting
value as a reusable pure expression. For other monads, bind `run` and use `value`.
Storing an unevaluated expression with `let` does not memoize it. Comparisons are
effectful methods, not `BEq` or `LT` instances that would discard the effects.

For example, `x ← (x + 1).eval` updates a mutable `CostExpr` variable, and
`if ← x.lt y then ...` executes a comparison before choosing a branch.
The monad supplies sequencing and the cost interpreter; the wrapper supplies
arithmetic notation without adding global instances on every `m I`.
-/

@[expose] public section

universe v

namespace Python.Cost

structure CostExpr (m : Type → Type v) (I : Type) where
  run : m I

namespace CostExpr

/-- Lift a value; reusing this expression performs no earlier operations again. -/
def value {I : Type} {m : Type → Type v} [Pure m] (x : I) : CostExpr m I := ⟨pure x⟩

@[simp] theorem run_value {I : Type} {m : Type → Type v} [Pure m] (x : I) :
    (value (m := m) x).run = pure x := rfl

/-- Execute once and retain the resulting value for subsequent expressions. -/
def eval {I : Type} {m : Type → Type} [Monad m] (x : CostExpr m I) : m (CostExpr m I) := do
  return value (← x.run)

/-- Evaluating a bound value never repeats its earlier work. -/
@[simp] theorem run_value_cost {I : Type} (x : I) (model : Model) (initial : ℕ) :
    CostT.run (value (m := CostT Id) x).run model initial = (x, initial) := rfl

/-- Assignment retains all charges and wraps only the computed value. -/
theorem run_eval {I : Type} (x : CostExpr (CostT Id) I) (model : Model) (initial : ℕ) :
    CostT.run x.eval model initial =
      let (a, total) := Id.run (CostT.run x.run model initial)
      (value a, total) := rfl

variable {I : Type} [PythonInt I] {m : Type → Type v} [Monad m] [MonadCost m]

def unary (op : I → m I) (x : CostExpr m I) : CostExpr m I := ⟨do
  op (← x.run)⟩

def binary (op : I → I → m I) (x y : CostExpr m I) : CostExpr m I := ⟨do
  let a ← x.run
  let b ← y.run
  op a b⟩

instance (n : ℕ) [OfNat I n] : OfNat (CostExpr m I) n := ⟨value (OfNat.ofNat n)⟩
instance : Add (CostExpr m I) := ⟨binary Int.add⟩
instance : Sub (CostExpr m I) := ⟨binary Int.sub⟩
instance : Neg (CostExpr m I) := ⟨unary Int.neg⟩
instance : Mul (CostExpr m I) := ⟨binary Int.mul⟩
instance : Div (CostExpr m I) := ⟨binary Int.floorDiv⟩
instance : Mod (CostExpr m I) := ⟨binary Int.mod⟩
instance : Pow (CostExpr m I) (CostExpr m I) := ⟨binary Int.pow⟩
instance : AndOp (CostExpr m I) := ⟨binary Int.bitAnd⟩
instance : ShiftLeft (CostExpr m I) := ⟨binary Int.shiftLeft⟩
instance : ShiftRight (CostExpr m I) := ⟨binary Int.shiftRight⟩

def bitCount (x : CostExpr m I) : CostExpr m I := unary Int.bitCount x
def bitLength (x : CostExpr m I) : CostExpr m I := unary Int.bitLength x

def eq (x y : CostExpr m I) : m Bool := do
  let a ← x.run
  let b ← y.run
  Int.eq a b

def lt (x y : CostExpr m I) : m Bool := do
  let a ← x.run
  let b ← y.run
  Int.lt a b

def truth (x : CostExpr m I) : m Bool := do Int.truth (← x.run)

@[simp] theorem run_add_id (x y : CostExpr Id I) : (x + y).run = (Id.run x.run) + (Id.run y.run) := rfl
@[simp] theorem run_sub_id (x y : CostExpr Id I) : (x - y).run = (Id.run x.run) - (Id.run y.run) := rfl
@[simp] theorem run_mul_id (x y : CostExpr Id I) : (x * y).run = (Id.run x.run) * (Id.run y.run) := rfl
@[simp] theorem run_neg_id (x : CostExpr Id I) : (-x).run = -(Id.run x.run) := rfl
@[simp] theorem run_div_id (x y : CostExpr Id I) : (x / y).run = (Id.run x.run) / (Id.run y.run) := rfl
@[simp] theorem run_mod_id (x y : CostExpr Id I) : (x % y).run = (Id.run x.run) % (Id.run y.run) := rfl
@[simp] theorem run_pow_id (x y : CostExpr Id I) : (x ^ y).run = (Id.run x.run) ^ (Id.run y.run) := rfl
@[simp] theorem run_bitAnd_id (x y : CostExpr Id I) :
    (x &&& y).run = (Id.run x.run) &&& (Id.run y.run) := rfl
@[simp] theorem run_shiftLeft_id (x y : CostExpr Id I) :
    (x <<< y).run = (Id.run x.run) <<< (Id.run y.run) := rfl
@[simp] theorem run_shiftRight_id (x y : CostExpr Id I) :
    (x >>> y).run = (Id.run x.run) >>> (Id.run y.run) := rfl
@[simp] theorem run_bitCount_id (x : CostExpr Id I) :
    x.bitCount.run = PythonInt.bitCount (Id.run x.run) := rfl
@[simp] theorem run_bitLength_id (x : CostExpr Id I) :
    x.bitLength.run = PythonInt.bitLength (Id.run x.run) := rfl

@[simp] theorem eq_id (x y : CostExpr Id I) :
    x.eq y = ((Id.run x.run) == (Id.run y.run)) := rfl
@[simp] theorem lt_id (x y : CostExpr Id I) :
    x.lt y = decide ((Id.run x.run) < (Id.run y.run)) := rfl
@[simp] theorem truth_id (x : CostExpr Id I) :
    x.truth = ((Id.run x.run) != 0) := rfl

/-- Unary notation executes its operand before charging the Python operation. -/
theorem run_unary_cost (op : IntOp) (f : I → I)
    (x : CostExpr (CostT Id) I) (model : Model) (initial : ℕ) :
    CostT.run (unary (Int.unary op f) x).run model initial =
      let (a, total) := Id.run (CostT.run x.run model initial)
      (f a, total + model (.integer ⟨op, [PythonInt.toInt a], PythonInt.toInt (f a)⟩)) := rfl

/-- Binary notation preserves left-to-right effects, then charges one operation.
This also applies when either operand already contains effectful arithmetic. -/
theorem run_binary_cost (op : IntOp) (f : I → I → I)
    (x y : CostExpr (CostT Id) I) (model : Model) (initial : ℕ) :
    CostT.run (binary (Int.binary op f) x y).run model initial =
      let (a, first) := Id.run (CostT.run x.run model initial)
      let (b, second) := Id.run (CostT.run y.run model first)
      (f a b, second + model (.integer
        ⟨op, [PythonInt.toInt a, PythonInt.toInt b], PythonInt.toInt (f a b)⟩)) := rfl

end CostExpr

end Python.Cost
