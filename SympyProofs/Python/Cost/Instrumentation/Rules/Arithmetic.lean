module

public import SympyProofs.Python.Cost.Instrumentation.Rules
public import SympyProofs.Python.Cost.Instrumentation.Loops

/-! Arithmetic rules use ordinary unary and binary constructor functions.
Each call names its operation and contract directly; no contract names are
assembled from strings and no separate arity or supported-operator table is needed.
New carriers can register their own rules for the same notation heads. -/

public meta section
namespace Python.Cost.Instrumentation

open CallPattern

def natArithmeticRules : OperationRules := #[
  OperationRule.binary ``HAdd.hAdd ``Checked.natAdd (const ``Nat),
  OperationRule.binary ``HSub.hSub ``Checked.natSub (const ``Nat),
  OperationRule.binary ``HMul.hMul ``Checked.natMul (const ``Nat),
  OperationRule.binary ``HDiv.hDiv ``Checked.natDiv (const ``Nat),
  OperationRule.binary ``HMod.hMod ``Checked.natMod (const ``Nat),
  OperationRule.binary ``HPow.hPow ``Checked.natPow (const ``Nat),
  OperationRule.binary ``BEq.beq ``Checked.natEq (const ``Nat),
  OperationRule.binary ``bne ``Checked.natNe (const ``Nat)
]

register_cost_rules natArithmeticRules

def intArithmeticRules : OperationRules := #[
  OperationRule.binary ``HAdd.hAdd ``Checked.intAdd (const ``Int),
  OperationRule.binary ``HSub.hSub ``Checked.intSub (const ``Int),
  OperationRule.binary ``HMul.hMul ``Checked.intMul (const ``Int),
  OperationRule.binary ``BEq.beq ``Checked.intEq (const ``Int),
  OperationRule.binary ``bne ``Checked.intNe (const ``Int),
  OperationRule.unary ``Neg.neg ``Checked.intNeg (const ``Int)
]

register_cost_rules intArithmeticRules

def pythonIntArithmeticRules : OperationRules := #[
  OperationRule.binary ``HAdd.hAdd ``Checked.pyAdd (.instanceOf ``PythonInt),
  OperationRule.binary ``HSub.hSub ``Checked.pySub (.instanceOf ``PythonInt),
  OperationRule.binary ``HMul.hMul ``Checked.pyMul (.instanceOf ``PythonInt),
  OperationRule.binary ``HDiv.hDiv ``Checked.pyDiv (.instanceOf ``PythonInt),
  OperationRule.binary ``HMod.hMod ``Checked.pyMod (.instanceOf ``PythonInt),
  OperationRule.binary ``HPow.hPow ``Checked.pyPow (.instanceOf ``PythonInt),
  OperationRule.binary ``HAnd.hAnd ``Checked.pyAnd (.instanceOf ``PythonInt),
  OperationRule.binary ``HShiftLeft.hShiftLeft ``Checked.pyShl (.instanceOf ``PythonInt),
  OperationRule.binary ``HShiftRight.hShiftRight ``Checked.pyShr (.instanceOf ``PythonInt),
  OperationRule.unary ``Neg.neg ``Checked.pyNeg (.instanceOf ``PythonInt),
  OperationRule.binary ``BEq.beq ``Checked.pyEq (.instanceOf ``PythonInt),
  OperationRule.binary ``bne ``Checked.pyNe (.instanceOf ``PythonInt),
  OperationRule.unary ``PythonInt.bitCount ``Checked.pyBitCount (.instanceOf ``PythonInt),
  OperationRule.unary ``PythonInt.bitLength ``Checked.pyBitLength (.instanceOf ``PythonInt)
]

register_cost_rules pythonIntArithmeticRules

def directCallRules : OperationRules := #[
  OperationRule.binary ``Int.fdiv ``Checked.intFdiv,
  OperationRule.unary ``Nat.sqrt ``Checked.natSqrt,
  OperationRule.unary ``Bool.not ``Checked.boolNot,
  OperationRule.unary ``ForInStep.yield ``Checked.stepYield,
  OperationRule.unary ``ForInStep.done ``Checked.stepDone
]

register_cost_rules directCallRules

end Python.Cost.Instrumentation
