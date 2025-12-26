# Feature: Control Flow (if/elif/else) — Feature #5

- **Importance**: 5/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## What was added
- Interpreter-style execution in `src/compiler/src/lib.rs` now evaluates `if/elif/else` statements and expression `if` nodes, honoring boolean/int truthiness.
- New system-style test `runner_handles_if_else_and_loops` verifies branch selection inside a `while` loop and accumulates even numbers only.

## Notes
- Truthiness: non-zero ints are true; `false`/`0` are false.
- `elif` branches are evaluated in order; `else` runs when nothing matches.

## Files touched
- `src/compiler/src/lib.rs` — added block/if execution.
- `src/driver/tests/runner_tests.rs` — new control-flow coverage.
