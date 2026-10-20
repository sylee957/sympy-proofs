module

public import SympyProofs.Python.Int

/-!
# Python bitwise operations

Inputs, counts, and results use `PythonInt`. The natural-number bit-count loop
used by the native implementation lives separately in `Bitwise.Nat`.
Negative integers are supported; shift counts must be nonnegative for Python
correspondence. Costed versions of these operations are in `Python.Cost.Int`.
-/

@[expose] public section

namespace Python.Bitwise

variable {I : Type} [PythonInt I]

abbrev bitCount (x : I) : I := PythonInt.bitCount x
abbrev bitLength (x : I) : I := PythonInt.bitLength x
abbrev and (x y : I) : I := x &&& y
abbrev shiftLeft (x count : I) : I := x <<< count
abbrev shiftRight (x count : I) : I := x >>> count

theorem shiftLeft_eq (x count : I) (h : 0 ≤ PythonInt.toInt count) :
    PythonInt.toInt (shiftLeft x count) =
      PythonInt.toInt x * 2 ^ (PythonInt.toNat count) :=
  PythonInt.toInt_shiftLeft x count h

theorem shiftRight_eq (x count : I) (h : 0 ≤ PythonInt.toInt count) :
    PythonInt.toInt (shiftRight x count) =
      (PythonInt.toInt x).fdiv (2 ^ (PythonInt.toNat count)) :=
  PythonInt.toInt_shiftRight x count h

end Python.Bitwise
