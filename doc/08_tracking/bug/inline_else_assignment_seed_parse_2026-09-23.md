# Inline else assignment fails in the deployed aarch64 seed

Status: OPEN grammar compatibility bug; AVX2 caller uses block-form assignment.

Review of PR #1431 at 5e35c81547c572e87a741836e636b5d862a1082d found that importing `src/compiler/70.backend/backend/native/isel_x86_64.spl` fails to parse in the deployed aarch64 seed. The two affected AVX2 planner arms end with `else: dest_id = dest.id` after an `if` / `elif` chain. The reviewer observed zero executed AVX examples, whereas main executed its existing examples.

Expected: the single-statement assignment after `else:` has the same semantics as an indented else block and permits the imported AVX2 tests to execute.

Minimal reproducer shape: initialize a mutable integer, branch through `if` and `elif`, and assign that integer in an inline `else: value = replacement`. Compare with the equivalent indented assignment block using the same deployed seed.

The scoped PR repair expands both assignments to indented blocks without changing their conditions or values. This records the compact-grammar limitation rather than claiming the parser itself is fixed. A follow-up parser regression must exercise both forms and require nonzero executed examples on the affected aarch64 compiler, then on the self-hosted phase compiler.

Bounded Windows bootstrap-seed diagnostic after the block-form repair: `test/02_integration/compiler/native/x86_avx512_mir_pipeline_spec.spl` reports `declared>=4 executed=4 passed=3 failed=1 skipped=0 dropped=0` and `Results: 4 total, 3 passed, 1 failed`. The remaining broad SIMD case fails with `avx512-copy-move-shape-mismatch`; the grammar repair is not a claim that the suite passes. This diagnostic used the deployed Rust bootstrap seed solely for parser compatibility, not as self-hosted phase verification. Independent aarch64 confirmation remains required.
