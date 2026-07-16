# Interpreter mixed integer/float ordering is rejected

- status: source fixed 2026-07-16; executable proof pending a runnable pure-Simple compiler artifact
- severity: high (valid ordered comparisons fail)
- component: live HIR evaluator and arena interpreter

## Symptom

`<`, `<=`, `>`, and `>=` rejected mixed integer/float operands even though
Simple widens the integer for ordered numeric comparison. Mixed-kind `==` and
`!=` remain deliberately type-strict.

## Resolution

Both interpreter paths now widen only the integer operand, in either operand
order, while retaining exact integer/integer comparisons and existing type
errors. Regressions cover every direction, equal numeric boundaries, and the
strict mixed-kind equality rule. The shared semantic helper now states the
same contract.
