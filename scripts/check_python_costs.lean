/-
Run after building the imported modules:
  lake env lean scripts/check_python_costs.lean

Checks lifted operations, evaluation order, reuse, mutable locals, base-monad
lifting, generator suspension, and the PythonInt buffer boundary.
-/
import SympyProofs.Binomial.Costs
import SympyProofs.Python.Cost.ByteArray
import SympyProofs.Python.Cost.SequenceWorstCase
import SympyProofs.Python.Int.Native
import SympyProofs.Python.ByteArray.Native

open PythonInt Python.Cost
open scoped PythonBytes

section Abstract

variable {I : Type} [PythonInt I]

def updates {m : Type → Type} [Monad m] [MonadCost m] (input : I) : m I := do
  let mut x : CostExpr m I := CostExpr.value input
  x ← (x + 1).eval
  x ← (x * x).eval
  x.run

example (x : I) : updates (m := Id) x = (x + 1) * (x + 1) := rfl
example (x : I) : CostT.run (updates (m := CostT Id) x) Models.operations =
    ((x + 1) * (x + 1), 2) := rfl

def reuse {m : Type → Type} [Monad m] [MonadCost m] (input : I) : m I := do
  let x : CostExpr m I := CostExpr.value input
  let y ← (x * x).eval
  let _ ← (y + 1).run
  (y - y).run

-- The multiply executes once; the discarded addition still counts.
example (x : I) : CostT.run (reuse (m := CostT Id) x) Models.operations =
    (x * x - x * x, 3) := rfl

-- A bare `let` stores a computation, so using it twice performs two multiplies.
def replay {m : Type → Type v} [Monad m] [MonadCost m] (input : I) : m I :=
  let x : CostExpr m I := CostExpr.value input
  let square := x * x
  (square - square).run

example (x : I) : CostT.run (replay (m := CostT Id) x) Models.operations =
    (x * x - x * x, 3) := rfl

def yielding (input : I) : CostT (Generator.Computation I) I := do
  let x : CostExpr (CostT (Generator.Computation I)) I := CostExpr.value input
  let result ← (x + 1).run
  Generator.yield result
  let y : CostExpr (CostT (Generator.Computation I)) I := CostExpr.value result
  (y * y).run

-- The multiplication and final cost stay inside the suspended continuation.
example (x : I) : CostT.run (yielding x) Models.operations =
    Generator.Computation.suspended (x + 1)
      (fun () => .done ((x + 1) * (x + 1), 2)) := rfl

def lifted (input : I) : CostT (Except String) I := do
  let input ← (pure input : Except String I)
  let x : CostExpr (CostT (Except String)) I := CostExpr.value input
  (x + 1).run

example (x : I) : CostT.run (lifted x) Models.operations = .ok (x + 1, 1) := rfl

def branching {m : Type → Type} [Monad m] [MonadCost m] (input : I) : m I := do
  let x : CostExpr m I := CostExpr.value input
  if ← x.lt 0 then
    (-x).run
  else
    (x * x + 1).run

def countdown {m : Type → Type} [Monad m] [MonadCost m] (input : I) : m I := do
  let mut x : CostExpr m I := CostExpr.value input
  while ← x.truth do
    x ← (x - 1).eval
  x.run

end Abstract

abbrev I := PythonInt.Native
abbrev B := PythonByteArray.Native
abbrev S := PythonBytes.Native

def runInt (program : CostT Id I) (model : Model) : ℤ × ℕ :=
  let (result, total) := Id.run (CostT.run program model)
  (toInt result, total)

def runExpr (program : CostExpr (CostT Id) I) (model : Model) : ℤ × ℕ :=
  runInt program.run model

-- Standard notation, signed floor arithmetic, and bitwise operations retain Python values.
#guard runExpr (2 + 3 * 4) Models.operations == (14, 2)
#guard runExpr (-7 / 3) Models.operations == (-3, 2)
#guard runExpr (-7 % -3) Models.operations == (-1, 3)
#guard runExpr ((-8 : CostExpr (CostT Id) I) >>> 2) Models.operations == (-2, 2)
#guard runExpr ((3 : CostExpr (CostT Id) I) <<< 4) Models.operations == (48, 1)
#guard runExpr (-7 &&& 3) Models.operations == (1, 2)
#guard runExpr (3 ^ (5 : CostExpr (CostT Id) I)) Models.operations == (243, 1)
#guard runExpr ((-7 : CostExpr (CostT Id) I).bitCount) Models.operations == (3, 2)
#guard runExpr ((256 : CostExpr (CostT Id) I).bitLength) Models.operations == (9, 1)
#guard Id.run (CostT.run ((1 : CostExpr (CostT Id) I).lt 2) Models.operations) == (true, 1)
#guard Id.run (CostT.run ((0 : CostExpr (CostT Id) I).truth) Models.operations) == (false, 1)

-- Only the selected branch executes; the final unsuccessful loop guard is charged.
#guard runInt (branching (-4 : I)) Models.operations == (4, 2)
#guard runInt (branching (4 : I)) Models.operations == (17, 3)
#guard runInt (countdown (4 : I)) Models.operations == (0, 9)
#guard runInt (countdown (0 : I)) Models.operations == (0, 1)

-- Neither plain values nor already evaluated integer expressions are implicitly lifted.
example : True := by
  fail_if_success have : CostExpr (CostT Id) I := (3 + 4 : ℕ)
  fail_if_success have : CostExpr (CostT Id) I := (3 + 4 : I)
  trivial

-- Search preserves signed -1 and charges only the inspected suffix in this model.
def bytes : B := bytearray (b[0x00, 0x01, 0x00, 0x01])
def one : S := b[0x01]
def noMatch : S := b[0x02]

#guard runInt (ByteArray.find bytes one (1 : I) (by decide) : CostT Id I)
    Models.byteReads == (1, 1)
#guard runInt (ByteArray.find bytes one (2 : I) (by decide) : CostT Id I)
    Models.byteReads == (3, 2)
#guard runInt (ByteArray.find bytes noMatch (1 : I) (by decide) : CostT Id I)
    Models.byteReads == (-1, 3)
#guard runInt (ByteArray.find bytes one (8 : I) (by decide) : CostT Id I)
    Models.byteReads == (-1, 0)

#guard PythonBytes.size ((CostT.run (Bytes.repeat one (-4 : I) : CostT Id S)
    Models.createdBytes).1) == 0
#guard (CostT.run (Bytes.repeat one (7 : I) : CostT Id S) Models.createdBytes).2 == 7
#guard (CostT.run (Python.Cost.ByteArray.set bytes (2 : I) (255 : I) : CostT Id B)
    Models.createdBytes).2 == 0
#guard PythonByteArray.IntAPI.get
    ((CostT.run (Python.Cost.ByteArray.set bytes (2 : I) (255 : I) : CostT Id B) Models.byteWrites).1)
    (2 : I) == 255

-- A replacement is read/written separately from its earlier allocation.
def replacement : S := b[0x00, 0x00]
def sliceProgram : CostT Id B :=
  ByteArray.setSlice bytes (1 : I) (2 : I) replacement (by decide) (by decide)
#guard (CostT.run sliceProgram Models.byteWrites).2 == 2
#guard (CostT.run sliceProgram Models.createdBytes).2 == 0
#guard PythonByteArray.toArray (CostT.run sliceProgram Models.operations).1 == #[0, 0, 0, 0]

-- Repricing the exact trace agrees with direct accumulation, including initial cost.
open SympyBinomial.PrimeExponent in
#guard (CostT.run (valuationM (m := CostT Id) I 1000 400) Models.schoolbook 17).2 ==
  17 + charge Models.schoolbook (TraceT.run (valuationM (m := TraceT Id) I 1000 400)).2

#print axioms SympyBinomial.PrimeExponent.valuation_run_eq_factorization

-- The asymptotic results concern these actual executed counters.
#guard runInt (Sequence.prod (#[] : Array I)) Models.schoolbook == (1, 1)
#guard runInt (Sequence.prod (#[2] : Array I)) Models.schoolbook == (2, 7)
#guard runInt (Sequence.prod (#[2, 2, 2, 2] : Array I)) Models.operations == (16, 9)
#guard runInt (Sequence.prod (#[2, 2, 2, 2] : Array I)) Models.schoolbook == (16, 43)

#print axioms SympyBinomial.PrimeExponent.valuation_isTheta_log2
#print axioms Python.Cost.Sequence.prod_schoolbook_isBigO
#print axioms Python.Cost.Sequence.prod_twos_isTheta
