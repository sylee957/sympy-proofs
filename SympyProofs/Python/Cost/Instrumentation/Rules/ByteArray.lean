module

public import SympyProofs.Python.Cost.Instrumentation.Rules.Bytes

/-! Bytearray operation and condition rules, independent of either cost interpreter. -/

public meta section
namespace Python.Cost.Instrumentation

open CallPattern

def byteArrayRules : OperationRules := #[
  { pattern := .app ``bytearray #[.capture `B, .capture `instance, .capture `bytes]
    contract := ``Checked.byteOfBytes, operands := #[`bytes]
    parameters := #[some `B, some `instance] },
  { pattern := .tail ``PythonByteArray.Value.len #[.capture `bytes]
    contract := ``Checked.byteLength, operands := #[`bytes] },
  { pattern := .tail ``PythonByteArray.Value.set!
      #[.capture `bytes, .capture `index, .capture `value]
    contract := ``Checked.byteSet, operands := #[`bytes, `index, `value] },
  { pattern := .tail ``PythonByteArray.Value.find
      #[.capture `bytes, .capture `value, .capture `start]
    contract := ``Checked.byteFind, operands := #[`bytes, `value, `start] },
  { pattern := .tail ``GetElem?.getElem!
      #[.typed (.capture `bytes) (.instanceOf ``PythonByteArray), .capture `index]
    contract := ``Checked.byteGet, operands := #[`bytes, `index] },
  { pattern := .app ``HMul.hMul
      #[.instanceOf ``PythonByteArray, .any, .any, .any, .capture `bytes, .capture `count]
    contract := ``Checked.byteRepeat, operands := #[`bytes, `count] },
  { pattern := .app ``decide
      #[.tail ``LT.lt #[.any, .tail ``PythonByteArray.Value.size #[.capture `bytes]], .any]
    contract := ``Checked.byteTruth, operands := #[`bytes] },
  { pattern := .app ``decide #[.app ``Ne #[const ``UInt8, .capture `value, .any], .any]
    contract := ``Checked.byteFlag, operands := #[`value] },
  { pattern := .app ``decide
      #[.app ``Ne #[const ``Int, .capture `x, .capture `y], .any]
    contract := ``Checked.signedNe, operands := #[`x, `y] }
]

register_cost_rules byteArrayRules

end Python.Cost.Instrumentation
