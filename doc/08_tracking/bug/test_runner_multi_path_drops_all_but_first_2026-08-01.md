# `simple test a.spl b.spl` silently runs ONLY the first spec and exits 0 — a failing second spec is dropped

**Status:** open
**Severity:** high (fail-open in the test runner itself)
**Found:** 2026-08-01
**Lane:** vacuous-spec audit
**Engine:** `bin/simple_seed test` — PROVED

## Symptom

When more than one spec path is passed on the command line, the runner executes
only the first and reports a summary covering that one file. The remaining paths
are neither run nor reported, and the exit code reflects only the first spec.

A failing spec passed as the second argument is therefore invisible: the command
exits **0**.

## Reproduction (PROVED)

Two probe specs, one green and one red:

    # ctrl_pass_spec.spl
    describe "control":
        it "passes":
            expect 1 to_equal 1

    # ctrl_fail_spec.spl
    describe "control":
        it "fails":
            expect 1 to_equal 2

Each alone behaves correctly:

    $ simple_seed test test/_probe/ctrl_pass_spec.spl
    rc=0   Results: 1 total, 1 passed, 0 failed
    $ simple_seed test test/_probe/ctrl_fail_spec.spl
    rc=1   Results: 1 total, 0 passed, 1 failed

Both together:

    $ simple_seed test test/_probe/ctrl_pass_spec.spl test/_probe/ctrl_fail_spec.spl
    rc=0   Results: 1 total, 1 passed, 0 failed
    per-file lines emitted:  PASS test/_probe/ctrl_pass_spec.spl

`Files: 1`. The failing spec produced no PASS/FAIL line at all — it was not run,
not skipped-with-notice, not counted.

## Why this matters beyond ergonomics

Any wrapper, script, or CI step that batches spec paths onto one `simple test`
invocation reports GREEN while silently testing a single file. This is the same
class of defect as a vacuous spec — a green signal that covers nothing — but it
lives in the runner, so it can hide arbitrarily many real specs at once.

Audit follow-up owed: grep `scripts/` and CI for `simple test` invocations that
pass more than one path.

## Workaround in use

The vacuous-spec audit runs exactly one spec per invocation.

## Not fixed here

Recorded, not repaired — the audit lane does not own the runner CLI.
