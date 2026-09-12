# `simple test`: a child that died in 3ms was reported as a 930-second timeout

- **Status:** RESOLVED (2026-09-12) — the misreporting is fixed. The underlying
  early child death is a SEPARATE, still-open defect, now honestly labelled.
- **Severity:** P2 — wrong verdict, wrong duration, wrong triage owner
- **Lane:** macOS open-bugs round 2, LANE 3 (wrong output). Reproduces PR #584's
  "`bin/simple test` fast-fails with a spurious timeout while `bin/simple run`
  gets further" symptom.
- **Host:** macOS 25.5.0, Apple M4
- **Seed:** `/Users/ormastes/simple/build/cargo-r2/release/simple` (`stat -f '%z %m'` = `39528776 1789199850`)

## Symptom (reproduced before the fix)

`run` passes the spec 4/4. `test` on the same file, same binary, same tree:

```
S=$(date +%s); SIMPLE_TIMEOUT_SECONDS=0 timeout 900 <seed> test \
  test/01_unit/lib/common/spec/exists_check_assertion_generalization_spec.spl; \
  echo "elapsed=$(( $(date +%s) - S ))s"
```

```
exit=255 elapsed=4s
error: test-runner: code -1 (process_run_bounded killed the child at its budget) (outer bound 930000ms)
SPEC FILE VERDICT: ... failed=1 timeout=1 reason=outer-bound-timeout budget_ms=930000
```

Four seconds of wall clock, reported as a 930000ms (15.5 minute) timeout.

## Root cause

`src/app/test_runner_new/test_runner_client.spl`, `run_one_direct`:

```
val killed = code == -1 or code == 124 or code == 143 or code == 255
if killed and not has_verdict_line(out + err):
    print timeout_verdict_line(path, "outer-bound-timeout", outer_timeout_ms)
```

All four codes are KILL-SHAPED but **ambiguous**: each is produced both by the
outer bounded wait killing the child and by an ordinary early failure (255 in
particular is any worker error). The branch treated the ambiguous set as proof
of a timeout and then printed `budget_ms=<budget>` — a duration it never
measured. Nothing in the function read a clock at all, so the reported duration
could not have been anything but the budget.

Two false claims per occurrence: that the run lasted the budget, and that the
cause was a timeout. The second is the expensive one — it routes triage to the
timeout owner ("raise SIMPLE_TIMEOUT_SECONDS") for a fault that has nothing to
do with time.

## Fix

- `src/app/test_daemon/light_protocol.spl` — new pure
  `bounded_run_classification(code, elapsed_ms, outer_timeout_ms)` returning
  `"ran"` / `"timeout"` / `"early-death"`. Elapsed time is a required argument
  and never defaulted, because it is the only evidence separating the last two.
  The floor is `outer_timeout_ms - 30000`, matching the 30s grace the client
  already grants the inner single-runner. New `early_death_verdict_line` records
  the MEASURED elapsed time, the ambiguous exit code, `timeout=0` and
  `inconclusive=1` (the existing `no_response_verdict_line` shape — an
  infrastructure outcome, not a fabricated RED test result).
- `src/app/test_runner_new/test_runner_client.spl` — measures the run with
  `time_now_unix_micros()` either side of `process_run_bounded` and branches on
  the classifier. The genuine-timeout path is unchanged except that it now also
  prints the measured elapsed time.

## Evidence after the fix

```
exit=255 elapsed=6s
error: test-runner: code -1 (process_run_bounded killed the child at its budget) after 3ms,
  well inside the 930000ms outer bound — this is an early death, not a timeout
SPEC FILE VERDICT: ... executed=0 passed=0 failed=0 dropped=1 timeout=0 inconclusive=1
  reason=child-died-early exit_code=-1 elapsed_ms=3 budget_ms=930000
```

The measured 3ms is now visible, and it makes the real defect legible for the
first time. Probed directly, the inner single-runner had the diagnosis all
along:

```
<seed> test --no-session-daemon --timeout 900 <spec>
  -> rc=5, Duration: 3ms
  UNVERIFIED <spec>: TERMINATED: child produced no exit status -- spawn or reap
    failure at the process layer, not a timeout and not a signal death
```

So the inner runner explicitly said "not a timeout" and the outer client
overrode it with "outer-bound-timeout". That underlying spawn/reap failure is
FILED as its own OPEN record —
`doc/08_tracking/bug/macos_test_child_spawn_or_reap_failure_no_exit_status_2026-09-12.md`
— not left to "whoever owns the lane". This record closes only the
misreporting.

## Specs (both required by .claude/rules/testing.md)

- Reproduce: `test/01_unit/app/test_runner_new/bounded_run_classification_spec.spl`
  — 5 examples, `5 examples, 0 failures`. Pins the measured incident (code -1 at
  3ms, code 255 at 4s), the grace boundary, and both verdict-line shapes.
- Generalize: `test/01_unit/app/test_runner_new/bounded_run_classification_generalization_spec.spl`
  — 4 examples, `4 examples, 0 failures`. Sweeps all four ambiguous codes across
  the duration range, pins the boundary against a second budget so it is derived
  rather than hardcoded, and pins that no ordinary exit code is ever
  reclassified.

## Sabotage triple (each mutation run, each observed RED, each reverted)

| # | mutation | result |
|---|---|---|
| D | classifier always returns `"timeout"` (restore the original defect) | `5 examples, 1 failure` |
| E | drop 255 from the kill-shaped set | `4 examples, 1 failure` (generalization) |
| F | `early_death_verdict_line` reports `budget_ms` in the `elapsed_ms` field | `5 examples, 1 failure` |
