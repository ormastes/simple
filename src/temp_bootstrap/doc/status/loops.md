# Feature: Loops (for/while/loop/break/continue) — Feature #6

- **Importance**: 5/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## What was added
- Exec engine in `src/compiler/src/lib.rs` now runs `while`, `loop`, and `for` over `range(...)` or array literals, honoring `break`/`continue`.
- `for` supports inclusive/exclusive ranges via `range(start, end, inclusive?)`.
- New tests exercise `break`/`continue` and loop accumulation.

## Files touched
- `src/compiler/src/lib.rs` — loop execution and range evaluation.
- `src/driver/tests/runner_tests.rs` — `runner_handles_if_else_and_loops`, `runner_handles_for_loop_and_break_continue`.
