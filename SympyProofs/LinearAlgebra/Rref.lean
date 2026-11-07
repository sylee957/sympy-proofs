module

public import SympyProofs.LinearAlgebra.Rref.Correctness
public import SympyProofs.LinearAlgebra.Rref.FractionField

/-! Reduced row echelon forms and their computation, in `SympyProofs.Rref`.

The modules separate certificate data (`Basic`), normalized field theory
(`Normalized`), fraction-field interpretation (`FractionField`), and Mathlib
uniqueness (`Uniqueness`). `Algorithm` implements elimination; `Invariants`
contains its mathematical preservation lemmas; `Correctness` verifies the loops
and states the public correctness and uniqueness results.

* `NormalizedRref` describes normalized field-valued RREF certificates. Its
  validity contract preserves the input's kernel, which determines the ordered
  pivots and the normalized matrix uniquely.
* `RrefResult` stores `(pivot column, unnormalized row)` pairs over an integral
  domain. There is no denominator field, required row order, or stored zero row.
  `RrefResult.normalized_valid` interprets these certificates in a fraction field;
  `RrefResult.equivalent_of_valid` expresses uniqueness by cross multiplication.
* `rref` performs monic Gauss–Jordan elimination over a field on an input of type
  `Vector (Vector F n) m`. It swaps pivots into consecutive rows, normalizes them,
  and eliminates above and below each pivot. It returns `RrefOutput F m n`, with
  `rows : Vector (Vector F n) m` and `pivots : Vector (Option (Fin n)) m`, including
  trailing zero rows. Correctness is proved separately from this data structure.
* `rref_isReducedRowEchelon` proves Mathlib's `Matrix.IsReducedRowEchelon` property.
  `rref_ker_eq` proves equality of kernels as subspaces; `rref_kernel_iff` gives
  the pointwise equivalence. `rref_isLeadingEntry_iff` identifies the returned
  pivot indices with Mathlib's leading entries.
* `Matrix.IsReducedRowEchelon.eq_of_ker_eq` proves that RREF matrices of the same
  shape with equal kernels are equal. `rref_function_unique` proves equality of
  any two matrix-valued functions that return RREF and preserve kernels.
  `rref_unique` and `rref_function_eq` identify such matrices and functions with
  the computed matrix output. These characterizations use Mathlib's predicates.
* `rref_output_unique` identifies the entire `RrefOutput` when its pivots also
  agree with the leading entries. `rref_algorithm_unique` proves that any
  implementation satisfying these three conditions is equal to `rref` itself.
* `rref_valid` exposes the completed elimination invariant.
  `RrefAlgorithm.Invariant.certificate_valid` connects the buffers to the
  abstract certificate theory.

These modules are independent of the generalized inverse construction.
-/
