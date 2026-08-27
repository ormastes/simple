# Interpreter logical operators eagerly evaluate the right operand

- status: source fixed 2026-07-15; executable interpreter proof pending a runnable pure-Simple compiler artifact
- severity: high (unexpected effects and errors)
- component: core tree-walking interpreter

## Symptom

`eval_binary` evaluated both operands before dispatching `and` or `or`.
Consequently `false and effect()` and `true or effect()` still ran `effect`.

## Resolution

After evaluating the left operand, the shared evaluator now returns false for
a false `and` and true for a true `or` without evaluating the right operand.
Focused tests use division by zero on the skipped side and also cover both
paths where the right operand remains required.
