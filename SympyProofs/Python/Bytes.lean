module

public import Mathlib.Tactic

/-!
# Immutable Python bytes

`PythonBytes S` specifies literals, length, reads, and repetition on an abstract
carrier `S`. It provides no indexed or slice assignment. The scoped notation
`b[0x01]` denotes a one-byte literal, corresponding to Python's `b'\x01'`.
`b[0x01, 0x02]` denotes two bytes; it does not parse Python string syntax.

Indices are nonnegative, with Python correspondence restricted to valid reads.
Signed repetition counts use Python's empty-result convention for negative counts.
This models byte values, not Python exceptions or object identity.
-/

@[expose] public section

/-- Immutable bytes operations and laws, independent of their representation. -/
class PythonBytes (S : Type) where
  /-- Interpret a literal sequence of byte values. -/
  literal : Array UInt8 → S
  /-- Number of bytes, representing Python's `len`. -/
  size : S → ℕ
  /-- Read a byte; Python correspondence requires an in-bounds index. -/
  getByte : S → ℕ → UInt8
  /-- Repeat the entire immutable sequence a nonnegative number of times. -/
  repeatBytes : S → ℕ → S
  /-- A literal has exactly the specified length. -/
  size_literal : ∀ values, size (literal values) = values.size
  /-- Every valid position contains the byte specified by the literal. -/
  get_literal : ∀ values i (hi : i < values.size), getByte (literal values) i = values[i]
  /-- Repetition multiplies the length by the count. -/
  size_repeat : ∀ bytes count, size (repeatBytes bytes count) = size bytes * count
  /-- Repetition copies each byte from the corresponding position in the original block. -/
  get_repeat : ∀ bytes count i, i < size (repeatBytes bytes count) →
    getByte (repeatBytes bytes count) i = getByte bytes (i % size bytes)

namespace PythonBytes

variable {S : Type} [PythonBytes S]

/-- A bytes literal written as a sequence of byte values. -/
scoped macro "b[" values:term,* "]" : term => `(PythonBytes.literal #[$values,*])

instance : GetElem S Nat UInt8 (fun bytes i => i < size bytes) where
  getElem bytes i _ := getByte bytes i

instance : HMul S Nat S := ⟨repeatBytes⟩

/-- Negative Python repetition counts yield an empty bytes value. -/
instance : HMul S Int S := ⟨fun bytes count => repeatBytes bytes count.toNat⟩

/-- Integer-valued length for Python arithmetic. -/
def len (bytes : S) : ℤ := size bytes

/-- Observe the byte values without exposing their storage. -/
def toArray (bytes : S) : Array UInt8 :=
  Array.ofFn (fun i : Fin (size bytes) => getByte bytes i.val)

attribute [simp] size_literal

@[simp] theorem size_mul (bytes : S) (count : ℕ) :
    size (bytes * count) = size bytes * count := size_repeat bytes count

@[simp] theorem size_mul_int (bytes : S) (count : ℤ) :
    size (bytes * count) = size bytes * count.toNat := size_repeat bytes count.toNat

/-- Method notation for values of an abstract bytes carrier. -/
abbrev Value (S : Type) := S

namespace Value

abbrev size (bytes : Value S) : ℕ := PythonBytes.size bytes
abbrev len (bytes : Value S) : ℤ := PythonBytes.len bytes

end Value

end PythonBytes
