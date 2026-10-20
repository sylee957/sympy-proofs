module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Commands

/-!
# Instrumentation of monadic control flow

Implementation modules under `Monadic/` separate shared context (`Basic`),
primitive and storage operations (`Primitives`), sequencing and branches
(`Control`), loops and suspension (`Iteration`), recursive and helper calls
(`Recursion`), the dispatcher (`Translate`), and command registration (`Commands`).

This backend translates the elaborated body directly into the cost monad.
Unlike the finite `Checked` representation, it can retain `Lean.Loop` and
generator suspension. Termination and value preservation for these constructs
are proved separately from the translation, using the original algorithm's
input contract. Arithmetic fragments still use the audited primitive contracts.

`derive_costed_monadic source as target using [...] streams [...]` appends a
monad and its cost instance to the original parameters. Helper mappings must
refer to previously generated definitions (or definitionally equal adapters).
Stream adapters must equal a deferred, event-producing execution of a previously
generated generator. `derive_costed_generator source as target` produces its
body with an explicit yield callback and loop interpreter.

Supported control includes standard Id sequencing, while loops, list iteration,
the generator's dependent natural range, and the two-field state produced by
Lean's well-founded recursion elaborator. The original measure and decrease
proofs are retained. Proof-dependent indices keep their source expressions;
their instrumented evaluation records the source work, rather than charging
proofs or implementation bookkeeping. These counters model source operations,
not the runtime of this Lean instrumentation itself.

Notation and macros are resolved before this pass. Unsupported operations,
custom arithmetic/sequencing/iterator instances, computed function bindings,
and unbound arithmetic in recursive-call arguments are rejected. This is a
checked, deliberately limited translator, not universal support for all Lean
programs or a formally verified compiler. The algorithm's separate kernel-checked
execution and resource proofs remain required for unbounded loops and streams.
-/
