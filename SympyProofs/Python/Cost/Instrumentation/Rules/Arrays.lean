module

public import SympyProofs.Python.Cost.Instrumentation.Rules

/-! Array length and slice materialization use the same rules in both backends. -/

public meta section
namespace Python.Cost.Instrumentation

def arrayRules : OperationRules := #[
  { pattern := .app ``Array.size #[.any, .capture `values]
    contract := ``Checked.arraySize, operands := #[`values] },
  { pattern := .tail ``Std.Slice.toArray
      #[.app ``Array.toSubarray #[.any, .capture `values, .capture `lo, .capture `hi]]
    contract := ``Checked.arraySlice, operands := #[`values, `lo, `hi] }
]

register_cost_rules arrayRules

end Python.Cost.Instrumentation
