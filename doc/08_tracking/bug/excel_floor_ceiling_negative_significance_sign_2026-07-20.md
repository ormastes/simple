# Bug: `excel_floor`/`excel_ceiling` mishandle negative `significance` (should use `abs(significance)`)

Date: 2026-07-20

## Symptom

`test/01_unit/app/office/sheets/math_bridge_extended_spec.spl`:
```
✗ FLOOR rounds down to significance
    assert_equal failed: expected -4, got -3
✗ CEILING rounds up to significance
    assert_equal failed: expected -3, got -4
✗ FLOOR handles negative significance
    assert_equal failed: expected 9, got 12
✗ CEILING handles negative significance
    assert_equal failed: expected 12, got 9

23 examples, 4 failures
```

Command:
```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/app/office/sheets/math_bridge_extended_spec.spl --no-session-daemon
```

## Root cause

`src/app/office/sheets/math_bridge.spl:224-234`:
```
pub fn excel_floor(x: f64, significance: f64) -> f64:
    """Round toward zero to nearest SIGNIFICANCE."""
    if significance == 0.0:
        return 0.0
    math_floor(x / significance) * significance

pub fn excel_ceiling(x: f64, significance: f64) -> f64:
    """Round away from zero to nearest SIGNIFICANCE."""
    if significance == 0.0:
        return 0.0
    math_ceil(x / significance) * significance
```

Both use the raw (signed) `significance` in the division/multiplication. When
`significance` is negative, `x / significance` flips the direction of the
`floor`/`ceil` call, which flips the result's sign relative to the expected
FLOOR.MATH/CEILING.MATH-style semantics the spec tests for (round toward
-infinity / +infinity using the *magnitude* of significance, independent of
its sign):

- `excel_floor(-3.7, -1)`: expected -4.0 (floor(-3.7) using |sig|=1), got
  -3.0 (impl computes `floor(-3.7 / -1) * -1 = floor(3.7) * -1 = -3.0`).
- `excel_ceiling(-3.2, -1)`: expected -3.0, got -4.0 (same sign-flip issue).
- `excel_floor(10.0, -3)`: expected 9.0 (floor(10/3)*3 using |sig|=3), got
  12.0 (impl computes `floor(10/-3)*-3 = floor(-3.33)*-3 = -4*-3 = 12.0`).
- `excel_ceiling(10.0, -3)`: expected 12.0, got 9.0 (same issue, inverted).

All 4 expected values are self-consistent with using `abs(significance)` for
the magnitude while `excel_floor` always rounds toward -infinity and
`excel_ceiling` always rounds toward +infinity (verified against all 8
assertions across the 2 affected `it` blocks, including the 6 that already
pass with positive significance where `significance == abs(significance)` so
the bug is masked).

## Suggested fix (not applied — semantic change, out of shard scope)

```
pub fn excel_floor(x: f64, significance: f64) -> f64:
    if significance == 0.0:
        return 0.0
    val sig = math_abs(significance)
    math_floor(x / sig) * sig

pub fn excel_ceiling(x: f64, significance: f64) -> f64:
    if significance == 0.0:
        return 0.0
    val sig = math_abs(significance)
    math_ceil(x / sig) * sig
```
(exact `abs` helper name TBD — check what's already imported in
`math_bridge.spl`, e.g. `math_abs` per its own `math_*` naming convention.)

## Affected

- `test/01_unit/app/office/sheets/math_bridge_extended_spec.spl` (4 of 23 examples)
