module

public import SympyProofs.Python.Cost
public import SympyProofs.Python.Bitwise

/-!
# Costed Python integer operations

Each call emits one event. Operands and results remain `PythonInt` values;
observations in events are mathematical integers. The pure value model's domain
contracts still apply: nonzero divisors and nonnegative powers/shift counts.
Using the total Lean operation outside those domains does not model Python's
exceptions or floating-point exponentiation.
-/

@[expose] public section

universe v

namespace Python.Cost.Int

variable {I : Type} [PythonInt I] {m : Type → Type v} [Monad m] [MonadCost m]

def unary (op : IntOp) (f : I → I) (x : I) : m I :=
  perform (.integer ⟨op, [PythonInt.toInt x], PythonInt.toInt (f x)⟩) (f x)

def binary (op : IntOp) (f : I → I → I) (x y : I) : m I :=
  perform (.integer ⟨op, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (f x y)⟩)
    (f x y)

abbrev add (x y : I) : m I := binary .add (· + ·) x y
abbrev sub (x y : I) : m I := binary .sub (· - ·) x y
abbrev neg (x : I) : m I := unary .neg (- ·) x
abbrev mul (x y : I) : m I := binary .mul (· * ·) x y
abbrev floorDiv (x y : I) : m I := binary .floorDiv (· / ·) x y
abbrev mod (x y : I) : m I := binary .mod (· % ·) x y
abbrev pow (x y : I) : m I := binary .pow (· ^ ·) x y
abbrev bitAnd (x y : I) : m I := binary .bitAnd (· &&& ·) x y
abbrev shiftLeft (x y : I) : m I := binary .shiftLeft (· <<< ·) x y
abbrev shiftRight (x y : I) : m I := binary .shiftRight (· >>> ·) x y
abbrev bitCount (x : I) : m I := unary .bitCount PythonInt.bitCount x
abbrev bitLength (x : I) : m I := unary .bitLength PythonInt.bitLength x

def eq (x y : I) : m Bool :=
  perform (.integer ⟨.eq, [PythonInt.toInt x, PythonInt.toInt y], if x == y then 1 else 0⟩)
    (x == y)

def lt (x y : I) : m Bool :=
  perform (.integer ⟨.lt, [PythonInt.toInt x, PythonInt.toInt y], if x < y then 1 else 0⟩)
    (decide (x < y))

/-- Python `bool(x)`, including negative integers. -/
def truth (x : I) : m Bool :=
  perform (.integer ⟨.truth, [PythonInt.toInt x], if x == 0 then 0 else 1⟩) (x != 0)

@[simp] theorem unary_id (op : IntOp) (f : I → I) (x : I) :
    unary (m := Id) op f x = f x := rfl

@[simp] theorem binary_id (op : IntOp) (f : I → I → I) (x y : I) :
    binary (m := Id) op f x y = f x y := rfl

@[simp] theorem run_unary (op : IntOp) (f : I → I) (x : I) (model : Model) (c : ℕ) :
    CostT.run (unary (m := CostT Id) op f x) model c =
      (f x, c + model (.integer ⟨op, [PythonInt.toInt x], PythonInt.toInt (f x)⟩)) := rfl

@[simp] theorem run_binary (op : IntOp) (f : I → I → I) (x y : I)
    (model : Model) (c : ℕ) :
    CostT.run (binary (m := CostT Id) op f x y) model c =
      (f x y, c + model (.integer
        ⟨op, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (f x y)⟩)) := rfl

end Python.Cost.Int
