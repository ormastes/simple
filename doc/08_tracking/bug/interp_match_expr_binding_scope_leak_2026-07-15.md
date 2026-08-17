# Interpreter match-expression bindings leak into caller scope

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## ALREADY_FIXED — verified 2026-08-17 (P2 triage, compiler lane)

Source verification at HEAD (no reproducer was ever recorded for this doc).

`src/compiler/10.frontend/core/interpreter/eval.spl:847` calls `env_push_scope()`
before `match_pattern`, with a matching `env_pop_scope()` on every exit path
(lines 851, 857, 872 guard-fail, 891 after the arm body). Arm bindings and the
`case X as name` form (line 885) are defined inside that scope, so they cannot
outlive the match expression. Closing as already fixed; no source change was
made by this lane. Per-symbol history is unavailable (this worktree history is
collapsed into the tree-restore commit `ae55a7467197`), so no fixing sha is
cited.
