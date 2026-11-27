# interp_u64_above_i64_max_signed_compare_and_print_2026-11-03

Fix: `uint64_word_eq` in `src/compiler_rust/compiler/src/interpreter/expr/ops.rs`
(commit 9d21958ee39) compares the 64-bit word for `UInt{64}` vs a negative `Int`.

## Regression evidence (2026-11-04)

`test/01_unit/compiler/interpreter/u64_field_parity_interp_jit_spec.spl` failed
(`a=false`) on `/home/yoon/dev/cargo-rel100/simple-rel` (built before the fix
was in the tree). The source at origin/release/1.0.0 (3ef23d69caa) already
contains the fix: a rebuild with no source change gives `a=true`, spec 1/1
passes. Not a code regression: the failing binary was stale (pending seed
redeploy, as the bug_db row says).

Remaining, not covered by the spec: `val lit = 0xFFFF_FFFF_FFFF_FFF0; print lit`
still prints `-16` (unsuffixed literal above i64::MAX is an `Int`).
