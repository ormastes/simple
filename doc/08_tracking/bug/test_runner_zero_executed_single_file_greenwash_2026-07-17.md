# Test runner: zero-executed spec exits 0 PASS on the single-file path

**Date:** 2026-07-17
**Severity:** high (greenwashing — a spec with zero real `it` executions reads as passing)
**Status:** fixed

## Symptom

`simple test <file.spl>` for a spec whose only content is `pending(...)` (or
any describe with zero real `it` executions) exits 0 with `Passed: 1`, PASS.

Repro (pre-fix): `<seed> test scripts/check/fixtures/font_evidence_runner_empty_spec.spl`
→ exit 0, `Passed: 1`, PASS.

## Root cause

The generic single-file `simple test <file>` route
(`src/app/test_runner_new/test_runner_client.spl` light-daemon client →
`src/app/test_daemon/light_daemon.spl` spawns
`src/app/test_runner_new/test_runner_single.spl <file> --no-session-daemon`)
inferred pass/fail purely from the raw child-process exit code plus a scan of
the aggregate `"N examples, M failures"` summary line. The interpreter's
intrinsic BDD reporter counts a `pending()` call as an executed example in
that summary line (`"1 example, 0 failures"`), so a file with zero real `it`
executions still parsed as "1 passed, 0 failed" and the process itself exited
0 — nothing in the single-file path ever checked whether an example had
*actually run*.

## Fix

`test_runner_single.spl` now counts REAL executed examples directly from the
interpreter's own per-example markers (✓ pass / ✗ fail glyphs, or the
compiled-mode textual `"... ok"` / `"... FAILED"` suffixes) via the new
`count_real_examples()` helper, instead of trusting the aggregate summary
line. If zero real examples were observed, the file fails closed with
`error: test-runner: no examples executed` regardless of exit code or the
(miscounting) summary line. When real failures are observed, it prints
`error: test-runner: spec failed`. The old summary-line parse
(`parse_child_example_summary`) is kept only as a fail-closed upper bound
(never allowed to reduce a failure count the glyph-based count found).

### Why NOT the usual result-wrapper contract

The multi-file interpreter path (`run_test_file_interpreter` in
`test_runner_execute.spl`) is supposed to close this exact gap via
`std.test_runner.test_result_wrapper.build_interpreter_result_wrapper`, which
wraps the source with `use std.spec.{print_summary, get_exit_code,
get_executed_test_count}` + a `panic(...)` on zero-executed / non-zero exit.
Reusing that exact contract here was attempted first (per the original fix
guidance) but discovered broken: seed to a sibling defect —
`doc/08_tracking/bug/std_spec_package_shadows_file_print_summary_2026-07-17.md`.
Wiring the existing wrapper in would have turned this narrow greenwash into a
universal false-RED (every green interpreter-mode spec fails to compile with
`function print_summary not found`), so the fix here is self-contained output
parsing instead — no cross-module `std.spec` dependency, and no new "result
wrapper" duplicate (per repo rule).

## Verification

- `timeout 240 src/compiler_rust/target/bootstrap/simple test scripts/check/fixtures/font_evidence_runner_empty_spec.spl` → exit 1, `error: test-runner: no examples executed`, `Failed: 1`, `FAIL`.
- `timeout 240 src/compiler_rust/target/bootstrap/simple test scripts/check/fixtures/font_evidence_runner_fail_spec.spl` → exit 1, `error: test-runner: spec failed`, `Failed: 1`, `FAIL` (unchanged outcome, message now present).
- A green one-`it` spec → exit 0, `Passed: 1`, `Failed: 0`, `PASS`.

## Cross-refs

Same greenwash family as
[[test_runner_60s_silent_kill_greenwash_2026-07-04]] and
[[test_runner_orphan_it_silently_ignored_2026-07-04]].
