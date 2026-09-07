# Interpreter mixed integer/float arithmetic is wrong or rejected

- status: **RESOLVED 2026-09-06 — executable proof landed.** (Was: "source fixed
  2026-07-15; executable interpreter proof pending a runnable pure-Simple
  compiler artifact".) No deployed self-hosted binary was needed — see
  "Executable proof (2026-09-06)" below.
- severity: high (silent wrong addition; unsupported valid arithmetic)
- component: core interpreter value operations

## Symptom

Mixed addition algebraically discarded the integer and doubled the float.
Mixed subtraction, multiplication, and division rejected the same supported
integer-to-float promotion entirely.

## Resolution

The shared arithmetic operations now explicitly widen the integer operand with
`f64(...)` in both operand orders. Focused tests cover all four operators plus
negative and zero addition controls.

## Executable proof (2026-09-06)

Spec: `test/01_unit/compiler_core/interpreter/mixed_numeric_arithmetic_spec.spl`
(10 `it` blocks: 5 reproduction, 2 record-named controls, 2 same-kind
generalization, 1 live-oracle control).

The "runnable pure-Simple compiler artifact" this record waited on was never
required. The spec imports
`compiler.core.interpreter.ops.{val_add, val_sub, val_mul, val_div}` and
`compiler.core.interpreter.value.*` directly, so the subject is
`src/compiler/10.frontend/core/interpreter/ops.spl` itself. Same technique and
same caveats as
`doc/08_tracking/bug/interp_logical_short_circuit_2026-07-15.md`.

Lane: `SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>` on the Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59) as host; subject is the pure-Simple `.spl` source read from the working
tree. No JIT or native-lane claim.

Discrimination proven by re-injecting the ORIGINAL defect described above —
`val_add`'s int+float branch returning `val_make_float(bf + bf)` (integer
discarded, float doubled) and `val_sub`'s int-then-float branch deleted so the
promotion is rejected — then re-measuring in the same tree with the same binary:

```
defect injected : Files: 1   Passed: 6   Failed: 4
restored        : Files: 1   Passed: 10  Failed: 0
```

`git diff --stat` on `ops.spl` was empty after restoring.

One `it` block deliberately drives a genuine type error (`i64 - nil`) and
asserts `ops_get_error()` contains `"type error"`, so the many
`expect(ops_get_error()).to_equal("")` assertions elsewhere are not vacuous.
