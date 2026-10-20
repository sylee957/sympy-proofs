module

public import SympyProofs.Python.Cost.Instrumentation.Rules
public import SympyProofs.Python.Cost.Instrumentation.Storage

/-! Bytes rules compose reusable literal and carrier patterns. -/

public meta section
namespace Python.Cost.Instrumentation

open CallPattern

def bytesCarrier : CallPattern :=
  .app ``PythonByteArray.Bytes #[.capture `B, .capture `instance]

def bytesRules : OperationRules := #[
  { pattern := .app ``OfNat.ofNat #[const ``UInt8, .capture `n, .any]
    contract := ``Checked.byteNumeral, operands := #[`n] },
  { pattern := .app ``PythonBytes.literal
      #[bytesCarrier, .any, singletonArray (.capture `value)]
    contract := ``Checked.byteLiteral, operands := #[`value]
    parameters := #[some `B, some `instance] },
  { pattern := .app ``HMul.hMul
      #[bytesCarrier, .any, .any, .any, .capture `bytes, .capture `count]
    contract := ``Checked.bytesRepeat, operands := #[`bytes, `count]
    parameters := #[some `B, some `instance] },
  { pattern := .app ``Neg.neg
      #[const ``Int, .any, .app ``OfNat.ofNat #[const ``Int, .capture `n, .any]]
    contract := ``Checked.negativeLiteral, operands := #[`n], monadicOnly := true }
]

register_cost_rules bytesRules

end Python.Cost.Instrumentation
