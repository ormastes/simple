# Interpreter float division `0.0 / 0.0` raises instead of producing NaN

- Status: OPEN
- Found: 2026-08-18, while writing C-MIG-0033 (`test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl`)
- Severity: correctness divergence from IEEE 754

## Repro

```
val x = 0.0 / 0.0
```

Under `bin/simple test` (tree-walk interpreter), this raises
`semantic: division by zero` and aborts the example instead of producing
`f64::NAN`, which is what IEEE 754 float division specifies and what the
`rt_math_is_nan` C/Rust oracle (`f64::is_nan`, backed by hardware division)
would receive as input if it ever performed this division itself.

Directly observed: `bin/simple test
test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl` failed with
`semantic: division by zero` on both the "domain-boundary values" example and
the 100-vector bulk-loop example, both of which used `0.0 / 0.0` as a second
NaN-construction path (alongside `pos_inf - pos_inf`). Removing that one
construction and replacing it with `(0.0 - pos_inf) + pos_inf` (also
canonically NaN, via inf + -inf, which does not go through the zero-divisor
special case) made the spec pass cleanly (5 examples, 5 passed).

## Root cause (not yet located)

Whatever implements the interpreter's binary `/` operator for float operands
appears to special-case a literal/runtime zero divisor and raise a semantic
error unconditionally, rather than checking whether the numerator is also
zero (which is the IEEE 754 NaN case) versus non-zero (which is the correctly
signed-infinity case). Both cases are being routed to the same "division by
zero" error path when the divisor is `0.0`, when only some integer-domain
callers actually want that behavior.

## Impact

Any pure-Simple code relying on IEEE 754 float semantics for `x / 0.0` (NaN
when `x == 0.0`, signed infinity otherwise) gets an interpreter panic/error
instead. This is a real semantic gap between the interpreter and hardware
float division, distinct from and additional to the already-tracked
run-vs-test JIT/interpreter divergence family
(`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`).

## Unblock condition

Locate the float `/` operator's zero-divisor handling (likely in the
tree-walk interpreter's binary-op evaluation, not in `interpreter_extern`)
and make it match IEEE 754: `0.0 / 0.0` -> NaN, nonzero `/ 0.0` -> signed
infinity, never a semantic error, for float operands specifically (integer
division by zero legitimately stays an error).

## Regression coverage

`test/01_unit/lib/common/numeric_round_is_nan_crosslang_spec.spl` documents
the workaround inline but does NOT assert the correct IEEE 754 behavior
(doing so would currently fail). A follow-up spec asserting `0.0 / 0.0`
produces NaN (not an error) should be added once this is fixed, and this doc
updated to RESOLVED with that spec cited.
