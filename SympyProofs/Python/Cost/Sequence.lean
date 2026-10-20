module

public import SympyProofs.Python.Cost.Int
public import SympyProofs.Python.Math

/-! # Costed list operations and the sequential multiplication inside `math.prod` -/

@[expose] public section

universe v

namespace Python.Cost.Sequence

variable {m : Type → Type v} [Monad m] [MonadCost m]

def empty {α : Type} : m (Array α) := perform (.sequence "empty" 0 0) #[]

def append {α : Type} (xs : Array α) (x : α) : m (Array α) :=
  perform (.sequence "append" 0 1) (xs.push x)

def length {α : Type} (xs : Array α) : m ℕ :=
  perform (.sequence "len" 0 0) xs.size

def slice {α : Type} (xs : Array α) (lo hi : ℕ) : m (Array α) :=
  let result := xs.extract lo hi
  perform (.sequence "slice" result.size result.size) result

def prod {I : Type} [PythonInt I] (xs : Array I) : m I := do
  let result ← xs.foldlM (fun result x => do
    MonadCost.emit (.control "prod.next")
    Python.Cost.Int.mul result x) 1
  MonadCost.emit (.control "prod.stop")
  return result

theorem prod_id {I : Type} [PythonInt I] (xs : Array I) :
    prod (m := Id) xs = Python.Math.prod xs := rfl

end Python.Cost.Sequence
