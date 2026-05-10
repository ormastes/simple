# simple-runtime Clippy Fix Progress

Date: 2026-04-28

## Summary

All clippy warnings in `simple-runtime` crate resolved. 0 warnings remain.

## Initial State

59 warnings (`-W clippy::all` pass with `RUSTFLAGS=""`):
- 25x `bool_assert_comparison` — `assert_eq!(x, true/false)` in tests
- 7x `useless_vec` — `vec![...]` where array suffices
- 6x `approx_constant` — `3.14159` literal instead of `std::f64::consts::PI`
- 5x `iter_count` / `repeat_take` — verbose iterator chains
- 5x `redundant_cast` — same-type casts (`usize as usize`)
- 3x `assert_true` — `assert!(true)`
- 2x `manual_range_contains`
- 2x `manual_range_contains` (inclusive)
- 1x `collapsible_if`
- 1x `enumerate_loop` — indexed loop over slice
- 1x `module_inception`
- 1x `manual_is_multiple_of`
- 1x `length_zero` — `.len() == 0`
- 1x `items_after_test_module`
- 1x `double_parens` + `unused_parens` (same site)

## Fixes Applied

### Batch 1: Auto-fix (41 suggestions applied by cargo clippy --fix)
- `cargo clippy --fix --no-deps -p simple-runtime --tests --allow-dirty --allow-staged -- -W clippy::all`
- Files touched (auto): `aop_around_tests.rs`, `vm_tests.rs`, `bytecode/tests.rs`,
  `value/mod_tests.rs`, `value/generator_tests.rs`, `value/bdd_ffi.rs`,
  `value/args.rs`, `value/ffi/atomic.rs`, `value/ffi/io_print.rs`,
  `value/ffi/random.rs`, `value/ffi/value_ops.rs`, `value/ffi/concurrent/arena.rs`,
  `value/serial.rs`, `value/wffi_native.rs`, `loader/package/format.rs`,
  `loader/smf/settlement.rs`, `loader/settlement/container_tests.rs`,
  `value/ffi/signature.rs`, `compress/upx_download.rs`

### Batch 2: Manual fixes (2 residual warnings)
- `runtime/src/value/ffi/io_print.rs:934,941` — replaced `3.14159` with `std::f64::consts::PI` (approx_constant; auto-fix not applied to tests)
- `runtime/src/bytecode/vm_tests.rs:868` — removed double parentheses `((count - 1))` → `count - 1` (double_parens + unused_parens)

## Final State

```
RUSTFLAGS="" cargo clippy --no-deps -p simple-runtime --all-targets
→ 0 warnings (no warning: lines except crate summary absent)
```

No `#[allow]` annotations added. All lints fixed at root.
No build.rs warnings found.
