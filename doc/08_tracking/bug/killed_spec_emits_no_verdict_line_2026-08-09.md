# Killed spec emits no verdict line — a broken spec reads as "not yet run"

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** high (fail-open; hides broken specs from every sweep)
- **Area:** `src/app/test_daemon/`, `src/app/test_runner_new/`

## Symptom

A spec killed at its per-file budget produced:

```
Process timed out
error: test-runner: file timed out
```

exit 255 (or 124/143/-1 depending on which layer killed it) and **no
`SPEC FILE VERDICT:` line at all**. Every sweep in this repo counts verdict
lines, so a killed spec was indistinguishable from a spec that had never been
scheduled — it read as *not yet run* rather than *broken*, and dropped out of
the failure list entirely.

This is what made stream G3's investigation
(`dap_breakpoint_system_spec_never_terminates_blocks_five_specs_2026-08-09.md`,
commit `a39229b1eb0`) so expensive: an apparent infinite hang was ~70 hours of
real work (`simple check` costs ~100 s/file, one worker per file), and both
leads in that bug doc were wrong. The thing that made it hard to see was
precisely the missing verdict.

## Root cause

Four independent timeout paths each returned a bare exit code:

| layer | file | path |
|-------|------|------|
| inner single-runner | `src/app/test_runner_new/test_runner_single.spl` | `code == -1 and stderr timed out` branch |
| daemon worker | `src/app/test_daemon/light_daemon.spl` | `handle_request` bounded run |
| client outer bound | `src/app/test_runner_new/test_runner_client.spl` | `run_one_direct` |
| client response wait | `src/app/test_runner_new/test_runner_client.spl` | `run_one_via_daemon` deadline; `src/app/test_daemon/main.spl` `cli_test_daemon_run` |

Each one *knew* the spec had been killed and reported it only in prose.

## Fix

`light_protocol.timeout_verdict_line()` emits a line whose field prefix is
byte-compatible with the driver's own `report_spec_file_verdict` output, so
every existing parser counts it as a real failure with no change:

```
SPEC FILE VERDICT: <path> declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=<why> budget_ms=<N>
```

`timeout=1` distinguishes a killed spec from an honestly-failing one; `reason=`
names the layer (`child-timeout`, `daemon-worker-timeout`,
`outer-bound-timeout`, `daemon-no-response`). All four paths now emit it, each
guarded by `has_verdict_line()` so a real verdict is never shadowed by a
synthetic one.

The 600 s duration is **unchanged** — the defect was the silence, not the
budget.

## Proof (real trigger, not a mock)

Fixture: `test/fixtures/test_infra/timeout_verdict_probe_spec.spl` (sleeps
600 s, run with `--timeout 5`). Binary:
`bin/release/x86_64-unknown-linux-gnu/simple`, 29577536 bytes, mtime
2026-08-09 04:50:31 (the Rust seed).

BEFORE (`git show HEAD:` copy of the runner):

```
Process timed out
error: test-runner: file timed out
```

`grep -c 'SPEC FILE VERDICT' = 0`, exit 1.

AFTER:

```
Process timed out
error: test-runner: file timed out
error: test-runner: code -1 (process_run_bounded killed the child at its budget) after 5s budget
SPEC FILE VERDICT: test/fixtures/test_infra/timeout_verdict_probe_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=child-timeout budget_ms=5000
Results: 1 total, 0 passed, 1 failed
```

`grep -c 'SPEC FILE VERDICT' = 1`, exit 1.

## See also

- `doc/07_guide/infra/testing.md` § Runner Operational Caveats, items F5/F6
- `stale_daemon_lock_fakes_total_red_2026-08-09.md`
