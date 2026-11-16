# Seed: unit comparison returns unit-wrapped bool (`true_fbytes`)

- **Status:** verification-pending
- **Date:** 2026-11-16
- **Lane:** rb4-unitcmp
- **Component:** Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter/expr/ops.rs` (unit/unit binary op branch)

## Repro

```simple
unit FreeBytes: i64 as fbytes
val a = 5 * 1_fbytes
print(a == 5_fbytes)   # printed `true_fbytes`, expected `true`
```

All six comparison operators (`== != < <= > >=`) were affected.

## Root cause

`check_unit_binary_op` (interpreter_unit.rs) correctly returns `Ok(None)` for a
same-family comparison ("returns bool, not a unit"), but the caller in
`ops.rs` treated every `Ok(_)` the same way and re-wrapped the inner result in
`Value::Unit { family: None.or(left family), suffix: left suffix }`.

## Fix

In `ops.rs`, comparison ops now return the inner comparison result directly
(plain `Value::Bool`). Mismatched-family comparison is unchanged: it is still
rejected by `check_unit_binary_op` with "different unit families".

Pure-Simple compiler: `src/compiler/30.types/units/unit_ops.spl` already types
unit comparisons as `bool` (`UnitOpVerdict.Allow("bool")`); no change needed.

## Tests

`test/01_unit/compiler/interpreter/unit_comparison_plain_bool_spec.spl` — all
six operators via string interpolation (detects the wrapper) plus an
`if a == b:` use.

Verified on rebuilt seed: spec 7/7 (deployed seed 1/7); `5_fbytes == 5_msx` (different families) still errors "Cannot compare ... different unit families".
