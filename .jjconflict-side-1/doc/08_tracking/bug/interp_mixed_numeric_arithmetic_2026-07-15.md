# Interpreter mixed integer/float arithmetic is wrong or rejected

- status: source fixed 2026-07-15; executable interpreter proof pending a runnable pure-Simple compiler artifact
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
