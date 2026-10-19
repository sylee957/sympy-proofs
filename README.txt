Experimental AI-assisted proofs

An experimental repository for Lean 4 / Mathlib proofs of mathematical
correctness in computer algebra systems, starting with SymPy.

Toolchain: Lean 4.35.0 with mathlib v4.35.0. Transitive dependency versions
are pinned in lake-manifest.json.

Build all proofs:
    lake build

Moore-Penrose pseudoinverses of 1-by-n and n-by-1 matrices:
    lake build SympyProofs.MoorePenrose

SympyProofs/MoorePenrose/RowColumn.lean proves that a nonzero real or complex row or
column matrix A has pseudoinverse A.H / sum_i |a_i|^2, and that the zero
matrix has pseudoinverse zero. It verifies all four Penrose equations and
uniqueness, including empty vectors. The entrywise formulas are
rowPinv_apply and colPinv_apply; isMoorePenrose_row_iff and
isMoorePenrose_col_iff characterize the unique solutions. Over the reals,
rowPinv_real and colPinv_real reduce A.H to the ordinary transpose.

The development lives in SympyProofs/MoorePenrose/, with the defining
equations and uniqueness in Basic.lean. Import SympyProofs.MoorePenrose
for the complete development. The related polynomial normalization experiment
is in sympy-benchmarks/pinv-normalization/.
