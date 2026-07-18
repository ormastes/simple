# Interpreter while-body locals leak into enclosing scope

- status: source fixed 2026-07-15; executable interpreter proof pending a runnable pure-Simple compiler artifact
- severity: high (silent caller-state mutation)
- component: core tree-walking interpreter

## Symptom

Both statement and expression `while` evaluators executed their bodies in the
enclosing environment. A body-local declaration could therefore overwrite an
outer binding and remain visible after the loop.

## Resolution

Each successful iteration now opens one body scope and closes it after the body
stops for normal completion, continue, break, return, or error. The regression
test runs two iterations and asserts that an outer same-named binding survives.
