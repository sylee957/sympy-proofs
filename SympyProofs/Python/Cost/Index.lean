module

public import SympyProofs.Python.Cost
public import Mathlib.Data.Nat.Sqrt

/-!
# Instrumentation at the natural-index boundary

Range bounds and storage indices retain Lean natural numbers in the verified
program. These adapters record their integer arithmetic. Natural subtraction
corresponds to Python only when the left operand is at least the right operand;
the algorithms use it on ordered slice bounds. Signed slice-count arithmetic
uses `Int.fdiv`, including the empty-slice case.
-/

@[expose] public section

universe v

namespace Python.Cost.Index

variable {m : Type → Type v} [Monad m] [MonadCost m]

def binary (op : IntOp) (f : ℕ → ℕ → ℕ) (x y : ℕ) : m ℕ :=
  perform (.integer ⟨op, [x, y], f x y⟩) (f x y)

abbrev add (x y : ℕ) : m ℕ := binary .add (· + ·) x y
abbrev sub (x y : ℕ) : m ℕ := binary .sub (· - ·) x y
abbrev mul (x y : ℕ) : m ℕ := binary .mul (· * ·) x y
abbrev div (x y : ℕ) : m ℕ := binary .floorDiv (· / ·) x y

def sqrt (x : ℕ) : m ℕ := perform (.integer ⟨.isqrt, [x], x.sqrt⟩) x.sqrt

def le (x y : ℕ) : m Bool :=
  perform (.integer ⟨.lt, [y, x], if y < x then 1 else 0⟩) (decide (x ≤ y))

def signed (op : IntOp) (f : ℤ → ℤ → ℤ) (x y : ℤ) : m ℤ :=
  perform (.integer ⟨op, [x, y], f x y⟩) (f x y)

def ne (x y : ℤ) : m Bool :=
  perform (.integer ⟨.eq, [x, y], if x = y then 1 else 0⟩) (decide (x ≠ y))

end Python.Cost.Index
