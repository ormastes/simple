# CLI app child-process hang (browser_cli_log_modes / cli_log_modes TIMEOUT class)

**Filed:** 2026-11-12, from phase-2 triage on release/1.0.0 (Windows host).
**Severity:** P1 — hangs any spec that spawns the `cli` app; both log-modes specs
TIMEOUT at the runner's 360s hard cap.
**Owner lane:** cli / dispatch.

## Symptom

Specs that invoke the `cli` application as a child process hang indefinitely;
the phase-2 runner records TIMEOUT after the hard kill:

- `test/02_integration/app/browser_cli_log_modes_spec.spl` — TIMEOUT (every run)
- `test/02_integration/app/cli_log_modes_spec.spl` — hang on its first example

The hang reproduces **with a clean environment** (no `SIMPLE_*` vars), so it is
independent of the test-runner env-leak fixed in PR #8640.

## Evidence

- The phase-2 runner hardening (file-redirected stdout, stdin from `/dev/null`,
  `timeout -k 10 360`) kills the child at the budget — the grandchild holds no
  pipe after the fix, yet the `cli` invocation still never completes, i.e. the
  process is alive and blocked (not output-starved). Earlier diagnosis observed
  the child holding the stdout pipe open forever; after the pipe fix the child
  still never exits.
- Agent-19's log-modes sweep (PR #8551) independently recorded: "`cli` app
  broken even with clean env".
- Adjacent log-modes apps (context, info, install, list, os, record, search)
  fail only on stderr-purity/oracle drift; `cli` is the sole hanger in the
  family, pointing at dispatch/entry shutdown rather than a harness issue.

## Suspects

- `src/app/cli/**` entry/dispatch path never reaching process exit (event loop /
  pending handle) on Windows UCRT.
- The `cli` startup route's app-server handshake (browser_cli variant) blocking
  on a connection that never arrives.

## Repro

```
bin/simple.exe test test/02_integration/app/browser_cli_log_modes_spec.spl --timeout 300
# or directly: spawn `bin/simple.exe cli --version`-class child from a spec and wait
```

## Notes

- Not a test-harness defect: the same harness passes for every other
  log-modes app once the env leak is scrubbed.
- Not the seed banner: the banner prints to stderr and exits 0 elsewhere.
