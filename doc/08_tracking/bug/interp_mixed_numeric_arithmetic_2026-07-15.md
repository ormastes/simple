# Interpreter mixed integer/float arithmetic is wrong or rejected

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Source verification at HEAD (no reproducer was ever recorded for this doc).

`src/compiler/10.frontend/core/interpreter/ops.spl` widens for BOTH operand
orders across all four arithmetic operators (lines 37, 45, 60, 65, 76, 81, 96,
101), e.g. `return val_make_float(f64(val_get_int(a)) - val_get_float(b))`.
Mixed int/float arithmetic is promoted correctly. Closing as already fixed; no
source change was made by this lane.
