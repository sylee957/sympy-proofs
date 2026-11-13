module

public import SympyProofs.Calculus.Exponential.Evaluator
public import SympyProofs.Calculus.Exponential.Real
public import SympyProofs.Calculus.Exponential.Complex
public import SympyProofs.Calculus.Exponential.Analytic

/-!
# Higher derivatives of the exponential of a function

* `Evaluator`: the shared recurrence and a verified imperative evaluator for the final factor.
* `Real`: real derivative formulas and `HasDerivAt` witnesses.
* `Complex`: complex derivative formulas and `HasDerivAt` witnesses.
* `Analytic`: local analytic formulas and derivative witnesses.

All declarations remain in the `SympyProofs.Calculus.Exponential` namespace.
-/
