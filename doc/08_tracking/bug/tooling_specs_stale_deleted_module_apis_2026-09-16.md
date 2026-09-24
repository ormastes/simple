# Tooling specs reference deleted module APIs (tooling.TodoItem, count_authored_examples)

Date: 2026-09-16
Specs: test/01_unit/app/tooling/todo_parser_spec.spl, test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl

## Observed
- `todo_parser_spec.spl`: `error: runtime: Module "tooling" does not export 'TodoItem'` — 0 of 8 examples executed. The spec imports `tooling.TodoItem.*`, `tooling.ParseResult.*`, `tooling.ParseError.*` from a module that no longer exists anywhere in `src/` (git history shows `src/lib/*/src/tooling/` was removed; `test/unit/lib/*/src/tooling/tooling_facade_spec.spl` twins were deleted as orphaned in f9c660acff6).
- `test_result_wrapper_authored_count_spec.spl`: `semantic: function count_authored_examples not found` — 0 of 2 examples executed. No `src/lib/*/test_runner/test_result_wrapper.spl` defines it (they export `build_interpreter_result_wrapper` and helpers only).

## Impact
Both specs are fully red at load time; they exercise a ported-API contract that has no implementation to run against, so regressions in the replacement code paths are unobserved.

## Expectation
- Either re-point `todo_parser_spec.spl` at the surviving API (`std.nogc_sync_mut.hooks.detectors.todo` provides `TodoItem`, `parse_todo_db`; it has NO `ParseResult`/`ParseError`) and port the ParseResult scenarios to whatever parse contract is current, or delete the spec if the old parse API is permanently gone.
- Implement `count_authored_examples` in `std.test_runner.test_result_wrapper` (the authored-count guard the spec describes) or delete the spec.

## Unblock condition
A lane that lands the replacement API (or an explicit decision to delete the specs) — this is not fixable by a stale-import edit because the imported symbols no longer exist under any path.
