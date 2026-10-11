# Copy propagation declared helper names

Requirement: **REQ-COPYPROP-DECLARED-NAME**. Executable spec: `test/01_unit/compiler/mir_opt/copy_propagation_declared_methods_spec.spl`.

Call instruction propagation for a load with destination local 17 and pointer local 7. The output remains a load, preserves destination 17, and preserves the pointer's Copy operand kind and local 7.

Call terminator propagation for a return with Copy local 5. The output remains a return and preserves both the Copy operand kind and local 5. Both scenarios require the pass to resolve the operand helper under its actual declared name.

The spec has two examples and real payload assertions; alternative instruction or operand kinds fail explicitly. It neither invokes the full optimization pass nor asserts that its existing quarantine is lifted.

Actual Stage1 TDD evidence: baseline two examples failed with the missing-method diagnostic; the unchanged examples both passed after the fifteen call names were corrected. Both runs closed their Windows Jobs and kept source/runtime/control hashes unchanged. Runtime: immutable Rust bootstrap seed `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`, explicit Phase1 routing, private Windows section specialization. This manual documents the scoped execution and makes no full-suite or native-product qualification claim. Exact case logs and hashes are retained in the bug report's evidence paths.
