# Native typed array equality falls through to handle comparison

Status: isolated candidate; native qualification pending. Base `7d2a71199c0`.

The authored `native_array_mutation_methods` diagnostic built successfully with
producer `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`
and failed 11/20 runtime checks on each of Cranelift and LLVM. Ten common failed
checks compare an array against a separately allocated array using `==`.
Several indexed-element and length checks pass. This pattern alone does not
prove mutations are correct; retain the original tests unchanged.

Source cause: `_MirLoweringExpr/expr_dispatch.spl` selects tag-aware
`rt_native_eq` only when a local carries HIR `Any`. Two typed arrays therefore
reach a raw MIR word comparison. The existing runtime equality implementation
already compares registered array contents, including nested arrays. Its
registered-array admission accepts tagged handles or aligned raw registered
pointers and checks membership before dereferencing; unrelated values are not
admitted as arrays.

The candidate extends only the Eq/NotEq gate to two proven runtime arrays and
preserves their handle representation when paired with Any. Is/IsNot keep the
identity path. Operands are still lowered once before the gate. No C/runtime
change is needed.

Qualification: run the original 20-check mutation fixture unchanged and the
new 18-check typed-array equality fixture on both backends with a compiler
containing the lowering fix. Require mixed Any/typed/nil and non-array negative
cases, nested content, identity distinction, and evaluation-once behavior.
Additional adoption gates: actual tagged/raw/slice representation probes,
cyclic graph equality through the existing runtime boundary, alias/copy
mutation independence, bounded memory, large-array p50/p95 and fast self
comparison. Do not infer a leak or ten mutation bugs from the current failures.

Two backend-specific failures remain separate: Cranelift empty-pop None and
LLVM byte-pop value. This equality patch does not claim to fix either.
