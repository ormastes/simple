# Interpreter mixed integer/float arithmetic is wrong or rejected

- status: source fixed 2026-07-16; executable interpreter proof pending a runnable pure-Simple compiler artifact
- severity: high (silent wrong addition; unsupported valid arithmetic)
- component: core interpreter value operations

## Symptom

Mixed addition algebraically discarded the integer and doubled the float.
Mixed subtraction, multiplication, and division rejected the same supported
integer-to-float promotion entirely.

## Resolution

The live HIR evaluator's `eval_binop` now widens the integer operand with
`.to_f64()` in both operand orders. The arena evaluator's `val_*` operations
already perform the same promotion with `f64(...)`. Direct HIR-backend tests
cover all six new operand-order branches and both mixed zero-divisor errors;
the arena regression covers all four operators plus negative and zero addition
controls.
