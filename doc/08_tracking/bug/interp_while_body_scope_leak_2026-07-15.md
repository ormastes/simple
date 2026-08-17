# Interpreter while-body locals leak into enclosing scope

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Source verification at HEAD (no reproducer was ever recorded for this doc).

`src/compiler/10.frontend/core/interpreter/eval_stmts.spl:593-620`: each
while-iteration pushes a child environment (`env_push_scope()`, ~line 610) and
pops it after the body. The same push/pop bracketing is present for for-loop
bodies at `eval_stmts.spl:444/451` and `528/536`, so body locals cannot leak
into the enclosing scope. Closing as already fixed; no source change was made by
this lane. Per-symbol history is unavailable (history collapsed into
`ae55a7467197`), so no fixing sha is cited.
