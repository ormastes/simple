# MC/DC interpreter fallback reports a budget kill as an unexplained signal death

- Status: fixed (branch `work/test-runner-whole-suite`)
- Found: 2026-10-19, `simple test test/01_unit/lib/common/crypto` under the seed built from `59d84defe67`

## Defect

With MC/DC on (the default), nearly every spec fails its standalone-SMF compile and
re-runs through `run_test_file_mcdc_interpreter_fallback`
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:912`). That function
read `scoped_child.result.{stdout,stderr,exit_code}` and went straight to
`make_result_from_output`. It never checked `scoped_child.result.limit_exceeded`,
which the primary interpreter path (`:264`) and the SMF path (`:381`) both check.
A wall-clock budget kill shows up as a bare 143 with no `TIMEOUT` marker, so it was
classified as `TERMINATED: child died by signal ... earlyoom cannot be ruled out`.
That meant `timed_out` was false, the verdict line had no `timeout=1`, and every
timeout in a sweep was blamed on an outside killer.

Observed: `pbkdf2_native_perf_spec.spl` `TERM (120274ms)` against a 120 s budget.
Fixture repro: a never-ending spec with `--timeout 4` reported `TERM (4068ms)`.

## Fix

The fallback now returns `scoped_limit_exceeded_result(...)` when the scope reports a
limit. This is a new exported helper that applies the classes the primary path
uses (`limit_is_unverified`, `limit_exceeded_message`,
`timed_out = limit_type contains "timeout"`). It keeps the fallback's
`mcdc_skip_reason` and `degraded_reason` tags.

## Specs

- Reproducer: `test/01_unit/lib/test_runner_mcdc_fallback_timeout_spec.spl`
  "reports a budget kill as TIMEOUT". It drives the real `simple test <dir>` lane over
  `test/fixtures/test_runner_mcdc/spin_fixture.spl` with a 3 s budget. It failed
  before the fix (no `timeout=1`) and passes after.
- Generalization (same file): a spec that finishes inside its budget on the same
  lane is still a real result, and memory/cpu/procs limits keep their classes
  (unverified vs real failure) through the helper.
