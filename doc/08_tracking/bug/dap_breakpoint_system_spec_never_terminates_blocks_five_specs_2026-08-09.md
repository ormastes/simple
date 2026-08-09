# `dap_breakpoint_system_spec` never terminates, respawns orphans, blocks 5 specs

**Status:** OPEN — cause NOT established
**Found:** 2026-08-09 by stream P3 (host `DebugTarget` adapter), across ~2h of attempts
**Severity:** blocks measurement of 5 DAP system specs
**Component:** `test/03_system/tools/dap/dap_breakpoint_system_spec.spl` + the test runner's retry path

## Symptom

`test/03_system/tools/dap/dap_breakpoint_system_spec.spl` never completes. The
runner retries it **indefinitely**, spawning processes that outlive their parent
and reparent to init. Because the system-spec loop is sequential, it never
advances, so four sibling specs are never reached either:

- `test/03_system/tools/dap/breakpoint_system_spec.spl`
- `test/03_system/tools/dap/stack_trace_system_spec.spl`
- `test/03_system/tools/dap/stepping_system_spec.spl`
- `test/03_system/tools/dap/variables_system_spec.spl`
- `test/03_system/tools/dap/dap_protocol_live_spec.spl`

Observed exit code on the repeated attempts: **144**.

## What has been ruled out

- **Not the `kill_simple_monitor` watchdog.** Its log was checked and contains
  only RSS warnings for unrelated bootstrap / `git fsck` processes — nothing
  naming this spec. The documented "SIGTERMs any run >=60s at high CPU" behavior
  is therefore not the mechanism here.
- **Not caused by the P3 change.** Reproduced before any of P3's files entered a
  system run, and P3's tracked diff against `origin/main` was empty (purely
  additive new files), which makes a regression impossible in principle.

## What is NOT established

The cause. Exit 144 is unexplained. Two candidate leads, neither confirmed:

1. **144 = 128 + 16** would be a signal-16 termination. Worth checking what, if
   anything, raises it.
2. A sibling stream independently found that **`pkill -f <pattern>` matches its
   own wrapper command string** and kills the shell chain, also yielding exit
   144. If any cleanup path in the runner or the spec uses `pkill -f`, it may be
   killing itself. This is a hypothesis, not a finding.

## Why it matters beyond the five specs

A spec that never terminates and is retried forever is worse than a failing one:
it consumes a sequential runner indefinitely and produces no verdict line, so it
reads as "not yet run" rather than "broken". This is the same class of hazard as
the `lab_http_api_spec` un-sleeping poll loop fixed earlier on 2026-08-09 (a
one-digit typo made a guard unsatisfiable) — check the spec's own wait/poll
constants before assuming the defect is in the DAP server.

## Next step to settle it

Run the spec directly (not via the sequential system loop) under `strace -f`,
capture what raises the signal, and check whether the runner's retry is bounded.
A retry cap would at least convert an infinite hang into a reported failure.

## Related

- `doc/08_tracking/bug/lab_http_api_spec_never_completes_via_test_daemon_2026-08-08.md`
  (same shape, different spec; root cause was a poll-guard constant)
- Environment trap found alongside this one: a stale
  `.build/test_daemon_light/daemon.lock` makes EVERY spec exit 1 with
  `ERROR: test daemon timed out` and no verdict line, faking RED baselines.
  Fix: `rm -rf .build/test_daemon_light`.
