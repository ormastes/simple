# Interpreter match-expression bindings leak into caller scope

- status: source fixed 2026-07-15; executable interpreter proof pending a runnable pure-Simple compiler artifact
- severity: high (silent caller-state mutation)
- component: core tree-walking interpreter

## Symptom

`match` expressions bound identifier patterns before opening the arm scope.
A failed guard or completed arm therefore overwrote an outer variable with the
same name.

## Resolution

`eval_match_expr` now opens the arm scope before pattern matching and closes it
on pattern failure, guard failure/error, body error, and success. Focused tests
cover both a failed guard and a successful binding while asserting that the
outer value remains unchanged.
