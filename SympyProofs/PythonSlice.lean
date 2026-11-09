module

public import SympyProofs.PythonSlice.Range
public import SympyProofs.PythonSlice.Basic
public import SympyProofs.PythonSlice.Sampling
public import SympyProofs.PythonSlice.Canonical
public import SympyProofs.PythonSlice.Composition

/-!
# Python slicing

Public entry point for Python-style slicing of an array of arbitrary finite
length, in the namespace `SympyProofs.PythonSlice`.

* `PythonSlice/Range.lean`: operational signed ranges, their elements and lengths.
* `PythonSlice/Basic.lean`: raw slices, normalization, bounds and sign formulas.
* `PythonSlice/Sampling.lean`: sampling values, separate element and length proofs,
  their combined correspondence, and the concrete array interface.
* `PythonSlice/Canonical.lean`: resolve omitted arguments while preserving explicit
  bounds, with idempotence, sampling correctness, and normalized element and length formulas.
* `PythonSlice/Composition.lean`: compose canonical slices, preserving elements,
  lengths and sampling, with canonicalization and rebuilding identities.

`sample` and `sampleArray` are executable definitions with no proof arguments.
Their correctness assumptions belong to the theorems; zero stride returns an
empty sample as the model's convention for this invalid input.

The main theorems are `sampling_element`, `sampling_length`, and
`sampling_correspondence`. Each takes `first last stride : Option ℤ`, assumes
`stride.getD 1 ≠ 0`, and displays the normalization and sign-based formula
with `let` expressions, including explicit defaults for omitted bounds.

All formulas and proofs quantify over the dimension and integer slice parameters;
specializing them to concrete values is ordinary theorem instantiation.
-/
