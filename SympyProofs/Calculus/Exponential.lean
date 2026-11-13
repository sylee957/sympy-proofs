module

public import SympyProofs.Calculus.Exponential.Evaluator
public import SympyProofs.Calculus.Exponential.Real
public import SympyProofs.Calculus.Exponential.Complex
public import SympyProofs.Calculus.Exponential.Analytic

/-!
# Higher derivatives of the exponential of a function

* `Evaluator`: differential and Bell recurrences, with a verified imperative cache evaluator.
* `Real`: real derivative formulas and `HasDerivAt` witnesses.
* `Complex`: complex derivative formulas and `HasDerivAt` witnesses.
* `Analytic`: local analytic formulas and derivative witnesses.

All declarations remain in the `SympyProofs.Calculus.Exponential` namespace.

The cache evaluator agrees unconditionally with `expBellFactor`. Its agreement
with `expDerivFactor` is proved under real/complex `C^n` or local analyticity
hypotheses in the corresponding modules.
-/
