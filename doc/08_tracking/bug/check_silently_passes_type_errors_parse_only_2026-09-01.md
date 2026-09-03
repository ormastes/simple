# `simple check` silently passes type errors and undefined variables — it is parse-only (OPEN, structural)

## Symptom (measured 2026-09-01, seed md5 `f9bf124d933a0de0af5d999444234996`)

With the current seed deployed (the stale-seed decorator failure of
`check_broken_on_windows_stale_seed_decorator_2026-09-01.md` fixed), `check`'s
verdicts on four fixture classes:

| fixture | expected of a checker | actual |
|---|---|---|
| clean hello world | pass | rc=0 `All checks passed` — correct |
| unbalanced parens | reported | rc=1 `[parser_error] ...` naming the file — correct |
| `val x: i64 = "not a number"` | reported | **rc=0 `All checks passed (1 file(s))`** |
| `print(undefined_variable_xyz)` | reported | **rc=0 `All checks passed (1 file(s))`** |

A checker that exits 0 on broken input is the silent-green class this repo
keeps hitting: everything downstream reads GREEN from a tool that never looked.

## Root cause (file:line)

`check` is parse-only by construction. The worker `src/app/check/main.spl`
`check_one()` (line 204) calls `parse_module(source, path)` (line 243), collects
`parser_get_errors()` (line 246) plus `concurrency_api_lint_errors()` — a
text-level lint — and nothing else. No semantic pass, no type checker, is ever
invoked. Its imports (line 6) are `compiler.core.parser` only. This is a
deliberate cost trade: parse alone was measured at ~2s per function
declaration with a 15-25s pre-main import-closure cost per worker
(`check_costs_two_seconds_per_function_decl_2026-08-10.md`), so wiring the
semantic layer in multiplies a cost that is already the command's known pain
point.

## Why this was not "fixed" in the same change

Giving `check` a semantic tier is a structural change to the worker's cost
model and to `src/compiler` layering (which semantic entry point can run
per-file, interpreted, at acceptable cost), not a contained defect. Making the
spec assert the current behaviour would enshrine the silent green; making it
assert the desired behaviour would ship a permanently red spec. Both are
forbidden here, so the gap is filed instead and the shipped spec
(`test/01_unit/app/cli/check_broken_file_reports_error_spec.spl`) pins the
reported-not-crashed-not-silent contract on the error class `check` currently
owns (parse errors), with a header note requiring it to be widened to a
type-error fixture when this bug closes.

## Unblock condition

A per-file semantic/type-check entry point in `src/compiler` that the check
worker can call after `parse_module` at a bounded cost (or behind an opt-in
`--semantic` tier flag so the parse-only fast path survives), plus a measured
cost row extending the 2026-08-10 cost-model doc. When it lands: flip the
type-error fixture in `check_broken_file_reports_error_spec.spl` from
parse-broken to `val x: i64 = "not a number"` and require the diagnostic to
name the mismatch.
