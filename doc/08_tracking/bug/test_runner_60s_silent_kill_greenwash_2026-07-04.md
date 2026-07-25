# Test runner: spec file killed at ~60s budget still prints PASS

**Date:** 2026-07-04
**Severity:** high (greenwashing — killed tests read as passing)
**Status:** fixed (2026-07-17, single-file path)

## Symptom

A spec file whose cumulative runtime crosses the runner's ~60s per-file
budget is terminated mid-run (`Terminated`), yet the summary still prints
`PASS` for the file. `it` blocks after the kill point never execute and
their assertions are silently skipped.

## How found

Extending `test/01_unit/app/office/pptx_export_spec.spl` (9 OPC
package-building cases, ~63s baseline) with additional cases: the new cases
were killed mid-run while the file reported PASS. Verified by adding a
deliberate-fail case after the kill point — the failure was NOT counted.

## Workaround (in use)

Keep heavy spec files under the budget; put additional cases in a sibling
file (`pptx_layout_spec.spl` created for exactly this reason — see its
docstring). When extending any slow spec, re-run with a deliberate-fail
probe placed LAST in the file to prove the tail executes.

## Related

- Directory BATCH runs hang entirely (separate known runner/daemon issue).
- doc/08_tracking/bug/: see prior runner issues; test_result.md greenwashing
  fix (commit 1ae4c7d99fc) addressed per-describe sums, this is a different
  path (process kill, not sum).

## Next step

Runner should mark a killed spec file FAILED (nonzero exit propagated to the
file result) and print the kill reason. Likely site: per-file process budget
handling in src/app/test_runner_new/ (or its successor after the tree swap).

## Fix (2026-07-17)

Verified fixed on the single-file path (`src/app/test_runner_new/test_runner_single.spl`,
which the light daemon spawns for `simple test <file>`). The underlying kill
mechanism (`process_run_timeout` in `src/app/io/process_ops.spl` /
`src/lib/nogc_sync_mut/io/process_ops.spl`, hardened by the recent "preserve
bounded child polling" commit 2f9f56d889d) already correctly kills the child
and returns exit code `-1` with a `[TIMEOUT: Process killed after Ns]`
marker. What was missing was the runner layer trusting that signal: the fix
landed for [[test_runner_zero_executed_single_file_greenwash_2026-07-17]]
detects `code == -1` with a `[TIMEOUT:` marker in stderr FIRST, before any
other pass/fail inference, and reports `error: test-runner: file timed out`,
`Failed: 1`, nonzero exit, `FAIL` — the distinct message the original "Next
step" note asked for.

Repro/verification: a spec with `it "sleeps past budget": rt_sleep_ms(6000); expect(1).to_equal(1)`
run via `test_runner_single.spl <file> --timeout=1` → killed at ~1s, exit 1,
`error: test-runner: file timed out`, `Failed: 1`, `FAIL`
(`build/test-runner-timeout-check/sleepy_spec.spl` during verification).
A regression shape covering this is added to
`test/03_system/check/test_runner_single_example_failure_contract_spec.spl`
("fails the wrapper when a spec is killed at its per-file timeout budget").

Not separately re-verified here: the multi-file `run_test_file_interpreter`
path (`test_runner_execute.spl`) and `make_result_from_output`'s existing
`exit_code == -1 → timed_out: true, failed: 1` handling, which already look
correct by inspection and were the subject of the same-day bounded-polling
fix; flag for a follow-up if a killed run is ever observed to still read
green through that path specifically.
