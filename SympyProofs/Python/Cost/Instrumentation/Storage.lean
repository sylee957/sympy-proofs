module

public import SympyProofs.Python.Cost.Instrumentation.Primitives
public import SympyProofs.Python.Cost.BufferIndex
public import SympyProofs.Python.Generator

/-! Audited storage and generator-interface contracts. Slice assignment keeps the
existing positive-stride, equal-length input contract; its total cost adapter is
used only after the algorithm proof establishes those preconditions. -/

@[expose] public section
namespace Python.Cost.Instrumentation.Checked
open PythonByteArray
variable {B : Type} [PythonByteArray B]

def byteLiteral (B : Type) [PythonByteArray B] (value : UInt8) :
    Checked (PythonBytes.literal #[value] : Bytes B) :=
  primitive (.buffer {
    kind := .bytes, op := .literal, after := 1, written := 1, created := 1 }) _

def byteOfBytes (B : Type) [PythonByteArray B] (bytes : Bytes B) : Checked (bytearray bytes : B) :=
  let size := PythonBytes.size bytes
  primitive (.buffer {
    kind := .bytearray, op := .ofBytes, before := size, after := size,
    read := size, written := size, created := size }) _

def byteRepeat (bytes : B) (count : ℕ) : Checked (bytes * count) :=
  let size := PythonByteArray.size bytes * count
  primitive (.buffer {
    kind := .bytearray, op := .repeat, args := [count], before := PythonByteArray.size bytes,
    after := size, read := size, written := size, created := size }) _

def bytesRepeat (B : Type) [PythonByteArray B] (bytes : Bytes B) (count : ℤ) : Checked (bytes * count) :=
  let size := PythonBytes.size bytes * count.toNat
  primitive (.buffer {
    kind := .bytes, op := .repeat, args := [count], before := PythonBytes.size bytes,
    after := size, read := size, written := size, created := size }) _

def byteLength (bytes : B) : Checked (PythonByteArray.Value.len bytes) :=
  primitive (.buffer {
    kind := .bytearray, op := .len, before := PythonByteArray.size bytes,
    after := PythonByteArray.size bytes }) _

def byteGet (bytes : B) (i : ℕ) : Checked bytes[i]! :=
  primitive (.buffer {
    kind := .bytearray, op := .get, args := [i], before := PythonByteArray.size bytes,
    after := PythonByteArray.size bytes, read := 1 }) _

def byteSet (bytes : B) (i : ℕ) (value : UInt8) : Checked (Value.set! bytes i value) :=
  primitive (.buffer {
    kind := .bytearray, op := .set, args := [i, value.toNat],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, written := 1 }) _

def byteFind (bytes : B) (value : UInt8) (start : ℕ) : Checked (Value.find bytes value start) :=
  let result := Value.find bytes value start
  let visits := if result = -1 then PythonByteArray.size bytes - start else result.toNat + 1 - start
  primitive (.buffer {
    kind := .bytearray, op := .find, args := [start],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, read := visits }) _

def byteTruth (bytes : B) : Checked (decide (0 < Value.size bytes)) :=
  primitive (.control "sieve.truth") _

def byteFlag (value : UInt8) : Checked (decide (value ≠ 0)) :=
  primitive (.control "sieve.byteTruth") _

def signedNe (x y : ℤ) : Checked (decide (x ≠ y)) :=
  primitive (.integer ⟨.eq, [x,y], if x = y then 1 else 0⟩) _

def negativeLiteral (n : ℕ) : Checked (- (OfNat.ofNat n : ℤ)) := pure _

def byteNumeral (n : ℕ) : Checked (OfNat.ofNat n : UInt8) := pure _

/-- Audit a proof-argument API by its resolved function, before erasing proofs. -/
def sliceCall (B : Type) [PythonByteArray B] : Checked (@Value.setSlice B _) := pure _

/-- The guarded adapter agrees with the proof-argument API on its full domain. -/
theorem slice_run {m : Type → Type} [Monad m] [LawfulMonad m] [MonadCost m]
    (bytes : B) (start step : ℕ) (replacement : Bytes B)
    (hs : 0 < step) (hl : PythonBytes.size replacement = sliceLength bytes start step) :
    BufferIndex.setSlice (m := m) bytes start step replacement =
      perform (.buffer {
    kind := .bytearray, op := .setSlice, args := [start,step],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes,
    read := PythonBytes.size replacement, written := PythonBytes.size replacement })
        (Value.setSlice bytes start step replacement hs hl) := by
  simp only [BufferIndex.setSlice, hs, hl, ↓reduceDIte]

end Python.Cost.Instrumentation.Checked

namespace Python.Cost.Instrumentation.Source

def generatorPure {V α : Type} (a : α) : Generator.Computation V α := Pure.pure a
def generatorBind {V α β : Type} (a : Generator.Computation V α)
    (f : α → Generator.Computation V β) : Generator.Computation V β := Bind.bind a f

end Python.Cost.Instrumentation.Source

namespace Python.Cost.Instrumentation.Source

def idLoop {S : Type} (init : S) (body : Unit → S → Id (ForInStep S)) : Id S :=
  ForIn.forIn (⟨⟩ : Lean.Loop) init body

def generatorLoop {V S : Type} (init : S)
    (body : Unit → S → Generator.Computation V (ForInStep S)) : Generator.Computation V S :=
  ForIn.forIn (⟨⟩ : Lean.Loop) init body

def idStream {V S : Type} (stream : Generator.Computation V Unit) (init : S)
    (body : V → S → Id (ForInStep S)) : Id S := ForIn.forIn stream init body

def generatorRange {V S : Type} (range : Std.Legacy.Range) (init : S)
    (body : (p : ℕ) → p ∈ range → S → Generator.Computation V (ForInStep S)) : Generator.Computation V S :=
  ForIn'.forIn' range init body

end Python.Cost.Instrumentation.Source
