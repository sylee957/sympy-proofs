module

public import SympyProofs.Python.Cost
public import SympyProofs.Python.Bytes.Int

/-! # Costed immutable bytes operations using Python integer arguments -/

@[expose] public section

universe v

namespace Python.Cost.Bytes

variable {I S : Type} [PythonInt I] [PythonBytes S]
variable {m : Type → Type v} [Monad m] [MonadCost m]

/-- Materializing a literal charges its payload once; literal caching is not assumed. -/
def literal (S : Type) [PythonBytes S] (values : Array UInt8) : m S :=
  perform (.buffer {
    kind := .bytes, op := .literal, after := values.size,
    written := values.size, created := values.size }) (PythonBytes.literal values)

def len (I : Type) [PythonInt I] (bytes : S) : m I :=
  perform (.buffer {
    kind := .bytes, op := .len, before := PythonBytes.size bytes,
    after := PythonBytes.size bytes }) (PythonBytes.IntAPI.len I bytes)

def get (bytes : S) (index : I) : m I :=
  perform (.buffer {
    kind := .bytes, op := .get, args := [PythonInt.toInt index],
    before := PythonBytes.size bytes, after := PythonBytes.size bytes, read := 1 })
    (PythonBytes.IntAPI.get bytes index)

def «repeat» (bytes : S) (count : I) : m S :=
  let result := PythonBytes.IntAPI.repeat bytes count
  let size := PythonBytes.size result
  perform (.buffer {
    kind := .bytes, op := .repeat, args := [PythonInt.toInt count],
    before := PythonBytes.size bytes, after := size, read := size, written := size,
    created := size }) result

end Python.Cost.Bytes
