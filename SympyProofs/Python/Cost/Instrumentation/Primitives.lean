module

public import SympyProofs.Python.Cost.Instrumentation.Program
public import SympyProofs.Python.Int
public import Mathlib.Data.Nat.Sqrt
public import SympyProofs.Python.Cost.Sequence

/-! Primitive contracts used by the elaborated-term instrumenter.
Natural subtraction is truncated; signed Python division uses `Int.fdiv` or
`PythonInt`. Their existing valid-input contracts continue to apply.
The arithmetic result is the operation named in each type, and each contract
emits exactly one event. No arbitrary user function is registered implicitly. -/

@[expose] public section
namespace Python.Cost.Instrumentation.Checked

variable {I : Type} [PythonInt I]

def pyAdd (x y : I) : Checked (x + y) :=
  primitive (.integer ⟨.add, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x + y)⟩) _

def pySub (x y : I) : Checked (x - y) :=
  primitive (.integer ⟨.sub, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x - y)⟩) _

def pyMul (x y : I) : Checked (x * y) :=
  primitive (.integer ⟨.mul, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x * y)⟩) _

def pyDiv (x y : I) : Checked (x / y) :=
  primitive (.integer ⟨.floorDiv, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x / y)⟩) _

def pyMod (x y : I) : Checked (x % y) :=
  primitive (.integer ⟨.mod, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x % y)⟩) _

def pyPow (x y : I) : Checked (x ^ y) :=
  primitive (.integer ⟨.pow, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x ^ y)⟩) _

def pyAnd (x y : I) : Checked (x &&& y) :=
  primitive (.integer ⟨.bitAnd, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x &&& y)⟩) _

def pyShl (x y : I) : Checked (x <<< y) :=
  primitive (.integer ⟨.shiftLeft, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x <<< y)⟩) _

def pyShr (x y : I) : Checked (x >>> y) :=
  primitive (.integer ⟨.shiftRight, [PythonInt.toInt x, PythonInt.toInt y], PythonInt.toInt (x >>> y)⟩) _

def pyNeg (x : I) : Checked (-x) :=
  primitive (.integer ⟨.neg, [PythonInt.toInt x], PythonInt.toInt (-x)⟩) _

def pyBitCount (x : I) : Checked (PythonInt.bitCount x) :=
  primitive (.integer ⟨.bitCount, [PythonInt.toInt x], PythonInt.toInt (PythonInt.bitCount x)⟩) _

def pyBitLength (x : I) : Checked (PythonInt.bitLength x) :=
  primitive (.integer ⟨.bitLength, [PythonInt.toInt x], PythonInt.toInt (PythonInt.bitLength x)⟩) _

def pyEq (x y : I) : Checked (x == y) :=
  primitive (.integer ⟨.eq, [PythonInt.toInt x, PythonInt.toInt y], if x == y then 1 else 0⟩) _

def pyNe (x y : I) : Checked (x != y) :=
  primitive (.integer ⟨.eq, [PythonInt.toInt x, PythonInt.toInt y], if x == y then 1 else 0⟩) _

def pyLt (x y : I) : Checked (decide (x < y)) :=
  primitive (.integer ⟨.lt, [PythonInt.toInt x, PythonInt.toInt y], if x < y then 1 else 0⟩) _

def pyLe (x y : I) : Checked (decide (x ≤ y)) :=
  primitive (.integer ⟨.lt, [PythonInt.toInt y, PythonInt.toInt x], if y < x then 1 else 0⟩) _

def pyDecEq (x y : I) : Checked (decide (x = y)) :=
  primitive (.integer ⟨.eq, [PythonInt.toInt x, PythonInt.toInt y], if x = y then 1 else 0⟩) _

def pyNatCast (n : ℕ) : Checked (n : I) := pure _
def pyIntCast (n : ℤ) : Checked (n : I) := pure _
def intNatCast (n : ℕ) : Checked (n : ℤ) := pure _

def pyZero : Checked (0 : I) := pure _
def pyOne : Checked (1 : I) := pure _
def pyNumeral (n : ℕ) [n.AtLeastTwo] : Checked (ofNat(n) : I) := pure _

def intNumeral (n : ℕ) : Checked (ofNat(n) : ℤ) := pure _

def natAdd (x y : ℕ) : Checked (x + y) :=
  primitive (.integer ⟨.add, [x, y], ((x + y : ℕ) : ℤ)⟩) _

def natSub (x y : ℕ) : Checked (x - y) :=
  primitive (.integer ⟨.sub, [x, y], ((x - y : ℕ) : ℤ)⟩) _

def natMul (x y : ℕ) : Checked (x * y) :=
  primitive (.integer ⟨.mul, [x, y], ((x * y : ℕ) : ℤ)⟩) _

def natDiv (x y : ℕ) : Checked (x / y) :=
  primitive (.integer ⟨.floorDiv, [x, y], ((x / y : ℕ) : ℤ)⟩) _

def natMod (x y : ℕ) : Checked (x % y) :=
  primitive (.integer ⟨.mod, [x, y], ((x % y : ℕ) : ℤ)⟩) _

def natPow (x y : ℕ) : Checked (x ^ y) :=
  primitive (.integer ⟨.pow, [x, y], ((x ^ y : ℕ) : ℤ)⟩) _

def natEq (x y : ℕ) : Checked (x == y) :=
  primitive (.integer ⟨.eq, [x, y], if x == y then 1 else 0⟩) _

def natNe (x y : ℕ) : Checked (x != y) :=
  primitive (.integer ⟨.eq, [x, y], if x == y then 1 else 0⟩) _

def natDecEq (x y : ℕ) : Checked (decide (x = y)) :=
  primitive (.integer ⟨.eq, [x, y], if x = y then 1 else 0⟩) _

def natLt (x y : ℕ) : Checked (decide (x < y)) :=
  primitive (.integer ⟨.lt, [x, y], if x < y then 1 else 0⟩) _

def natLe (x y : ℕ) : Checked (decide (x ≤ y)) :=
  primitive (.integer ⟨.lt, [y, x], if y < x then 1 else 0⟩) _

def intAdd (x y : ℤ) : Checked (x + y) :=
  primitive (.integer ⟨.add, [x, y], x + y⟩) _

def intSub (x y : ℤ) : Checked (x - y) :=
  primitive (.integer ⟨.sub, [x, y], x - y⟩) _

def intMul (x y : ℤ) : Checked (x * y) :=
  primitive (.integer ⟨.mul, [x, y], x * y⟩) _

def intFdiv (x y : ℤ) : Checked (x.fdiv y) :=
  primitive (.integer ⟨.floorDiv, [x, y], x.fdiv y⟩) _

def intEq (x y : ℤ) : Checked (x == y) :=
  primitive (.integer ⟨.eq, [x, y], if x == y then 1 else 0⟩) _

def intNe (x y : ℤ) : Checked (x != y) :=
  primitive (.integer ⟨.eq, [x, y], if x == y then 1 else 0⟩) _

def intDecEq (x y : ℤ) : Checked (decide (x = y)) :=
  primitive (.integer ⟨.eq, [x, y], if x = y then 1 else 0⟩) _

def intLt (x y : ℤ) : Checked (decide (x < y)) :=
  primitive (.integer ⟨.lt, [x, y], if x < y then 1 else 0⟩) _

def intLe (x y : ℤ) : Checked (decide (x ≤ y)) :=
  primitive (.integer ⟨.lt, [y, x], if y < x then 1 else 0⟩) _

def natSqrt (x : ℕ) : Checked x.sqrt :=
  primitive (.integer ⟨.isqrt, [x], x.sqrt⟩) _

def intNeg (x : ℤ) : Checked (-x) :=
  primitive (.integer ⟨.neg, [x], -x⟩) _

def boolNot (x : Bool) : Checked (!x) :=
  primitive (.control "bool.not") _

/-- Audited zero-cost conversion from a Boolean to a Lean `if` condition. -/
def boolDecision (b : Bool) : Checked (decide (b = true)) := pure _

def arraySize {α : Type} (xs : Array α) : Checked xs.size :=
  primitive (.sequence "len" 0 0) _

def arraySlice {α : Type} (xs : Array α) (lo hi : ℕ) : Checked xs[lo:hi].toArray :=
  ⟨.primitive (.sequence "slice" (xs.extract lo hi).size (xs.extract lo hi).size)
    (xs.extract lo hi), by
    change xs.extract lo hi = xs[lo:hi].toArray
    symm
    apply Array.toList_inj.mp
    by_cases h : lo ≤ min hi xs.size
    · simp [Subarray.toList_eq, Subarray.toList_toArray, Nat.min_eq_left h,
        List.extract_eq_take_drop]
      omega
    · have hz : min hi xs.size ≤ lo := by omega
      simp [Subarray.toList_eq, Subarray.toList_toArray, Nat.min_eq_right hz,
        List.extract_eq_take_drop]
      omega⟩

/-- Audit the resolved `math.prod` arithmetic instances before using its loop contract. -/
def prodCall (xs : Array I) : Checked (Python.Math.prod xs) := pure _

end Python.Cost.Instrumentation.Checked
